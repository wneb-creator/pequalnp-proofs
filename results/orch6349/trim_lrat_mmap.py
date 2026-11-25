#!/usr/bin/env python3
"""Untrusted, bounded-memory preparation of positive-hint ASCII LRAT.

The Lean checker remains the proof authority. Indices and marking/remapping
vectors live in mmap files; no dependency graph or work stack is kept in RAM.
An incomplete growing proof can be indexed and resumed before UNSAT arrives.
"""
import argparse
import hashlib
import json
import mmap
import os
from pathlib import Path
import struct
import time


class Vector:
    def __init__(self, path, width, length=0, resume=False):
        self.width = width
        self.f = path.open('r+b' if resume else 'w+b')
        self.length = length
        size = max(self.f.seek(0, 2), 1 << 20, width * length)
        self.f.truncate(size)
        self.m = mmap.mmap(self.f.fileno(), size)
        self.fmt = '<Q' if width == 8 else '<I'

    def ensure(self, length):
        size = self.width * length
        if size > len(self.m):
            size = ((size + (1 << 20) - 1) >> 20) << 20
            self.m.resize(size)
        self.length = max(self.length, length)

    def get(self, i):
        if i >= self.length:
            return 0
        return self.m[i] if self.width == 1 else struct.unpack_from(self.fmt, self.m, i * self.width)[0]

    def set(self, i, value):
        self.ensure(i + 1)
        if self.width == 1:
            self.m[i] = value
        else:
            struct.pack_into(self.fmt, self.m, i * self.width, value)

    def close(self):
        self.m.flush()
        self.m.close()
        self.f.truncate(self.length * self.width)
        self.f.close()


def addition(f, offset, cid, max_line):
    f.seek(offset - 1)
    line = f.readline(max_line + 1)
    if len(line) > max_line or not line.endswith(b'\n'):
        raise ValueError(f'overlong or partial retained clause {cid}')
    fields = list(map(int, line.split()))
    if fields[0] != cid or fields[-1] != 0:
        raise ValueError(f'malformed retained clause {cid}')
    split = fields.index(0, 1)
    lits, hints = fields[1:split], fields[split + 1:-1]
    if any(h <= 0 or h >= cid for h in hints):
        raise ValueError(f'RAT, zero, or forward hint in retained clause {cid}')
    return lits, hints


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('proof', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--initial', type=int, required=True)
    ap.add_argument('--index-prefix', type=Path)
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--index-only', action='store_true')
    ap.add_argument('--max-line-bytes', type=int, default=16 << 20)
    a = ap.parse_args()
    started = time.monotonic()
    prefix = a.index_prefix or a.output.with_suffix('.index')
    meta_path = Path(str(prefix) + '.json')
    stat = a.proof.stat()
    meta = {'initial': a.initial, 'device': stat.st_dev, 'inode': stat.st_ino,
            'indexed_bytes': 0, 'maximum_id': a.initial, 'additions': 0,
            'deletions': 0, 'empty_id': 0}
    if a.resume:
        meta = json.loads(meta_path.read_text())
        if (meta['initial'], meta['device'], meta['inode']) != (a.initial, stat.st_dev, stat.st_ino):
            raise ValueError('index belongs to a different formula or proof file')
        if stat.st_size < meta['indexed_bytes']:
            raise ValueError('proof file was truncated after indexing')
    offsets = Vector(Path(str(prefix) + '.offsets.u64'), 8,
                     meta['maximum_id'] + 1, a.resume)
    snapshot = stat.st_size
    if not meta['empty_id']:
        with a.proof.open('rb') as f:
            f.seek(meta['indexed_bytes'])
            while f.tell() < snapshot:
                offset = f.tell()
                line = f.readline(a.max_line_bytes + 1)
                if len(line) > a.max_line_bytes:
                    raise ValueError(f'line exceeds configured bound at byte {offset}')
                if not line.endswith(b'\n') or f.tell() > snapshot:
                    break
                fields = line.split(maxsplit=2)
                if len(fields) < 2:
                    raise ValueError(f'malformed line at byte {offset}')
                cid = int(fields[0])
                if fields[1] == b'd':
                    meta['deletions'] += 1
                else:
                    if cid <= meta['maximum_id']:
                        raise ValueError(f'nonincreasing/reused addition ID {cid}')
                    offsets.set(cid, offset + 1)
                    meta['maximum_id'] = cid
                    meta['additions'] += 1
                    if fields[1] == b'0':
                        meta['empty_id'] = cid
                meta['indexed_bytes'] = f.tell()
                if meta['empty_id']:
                    break
    meta['snapshot_bytes'] = snapshot
    meta['index_seconds'] = round(time.monotonic() - started, 3)
    meta_path.write_text(json.dumps(meta, indent=2) + '\n')
    if a.index_only or not meta['empty_id']:
        offsets.close()
        print(json.dumps({'status': 'indexed', **meta}, indent=2))
        return

    needed = Vector(Path(str(prefix) + '.needed.u8'), 1, meta['maximum_id'] + 1)
    needed.set(meta['empty_id'], 1)
    retained = literals = hints_count = maximum_variable = 0
    with a.proof.open('rb') as f:
        for cid in range(meta['empty_id'], a.initial, -1):
            if not needed.get(cid):
                continue
            offset = offsets.get(cid)
            if not offset:
                raise ValueError(f'retained hint references missing clause {cid}')
            lits, hints = addition(f, offset, cid, a.max_line_bytes)
            retained += 1
            literals += len(lits)
            hints_count += len(hints)
            maximum_variable = max(maximum_variable, max(map(abs, lits), default=0))
            for h in hints:
                needed.set(h, 1)

    remap = Vector(Path(str(prefix) + '.remap.u32'), 4, meta['maximum_id'] + 1)
    next_id = 0
    initial_ids = []
    for cid in range(1, meta['maximum_id'] + 1):
        if needed.get(cid):
            next_id += 1
            if next_id >= 2 ** 32:
                raise ValueError('retained clause count exceeds u32 remapping capacity')
            remap.set(cid, next_id)
            if cid <= a.initial:
                initial_ids.append(cid)
    digest = hashlib.sha256()
    with a.proof.open('rb') as f, a.output.open('wb') as out:
        for cid in range(a.initial + 1, meta['empty_id'] + 1):
            if not needed.get(cid):
                continue
            lits, hints = addition(f, offsets.get(cid), cid, a.max_line_bytes)
            fields = [remap.get(cid), *lits, 0, *(remap.get(h) for h in hints), 0]
            if any(remap.get(h) == 0 for h in hints):
                raise ValueError('unmapped retained dependency')
            line = (' '.join(map(str, fields)) + '\n').encode()
            out.write(line)
            digest.update(line)
    report = {'status': 'trimmed; still requires independent logical checking',
              'input': str(a.proof), 'output': str(a.output), **meta,
              'retained_initial': len(initial_ids), 'retained_additions': retained,
              'retained_literals': literals, 'retained_hints': hints_count,
              'maximum_derived_variable': maximum_variable,
              'remapped_empty_id': remap.get(meta['empty_id']),
              'initial_ids_in_new_order': initial_ids,
              'remap_u32': str(prefix) + '.remap.u32',
              'bytes_out': a.output.stat().st_size, 'sha256_out': digest.hexdigest(),
              'total_seconds': round(time.monotonic() - started, 3)}
    a.output.with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
    offsets.close()
    needed.close()
    remap.close()
    print(json.dumps({k: v for k, v in report.items() if k != 'initial_ids_in_new_order'}, indent=2))


if __name__ == '__main__':
    main()
