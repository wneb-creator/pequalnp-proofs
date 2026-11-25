#!/usr/bin/env python3
"""Finite-field F4 diagnostics with atomic PARTIAL generator checkpoints.

SIGUSR1 saves at the next stable round boundary and continues; SIGUSR2 saves
and stops there. Resume is original input UNION checkpoint, not a saved pairset.
A partial checkpoint never supplies a Groebner-basis or nonexistence verdict.
"""
import argparse
from array import array
import ctypes as C
import gc
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import time

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for variable in tuple(os.environ):
    if variable not in {'PATH', 'LANG', 'LC_ALL', 'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'TMPDIR'}:
        os.environ.pop(variable, None)


def open_text(path):
    return gzip.open(path, 'rt') if str(path).endswith(('.gz', '.gz.previous')) else open(path)


def header(stream):
    comments = []
    for line in stream:
        if line.startswith('#'):
            comments.append(line.rstrip())
        elif line.strip():
            names = [x.strip() for x in line.strip().split(',')]
            break
    else:
        raise ValueError('empty polynomial input')
    if len(set(names)) != len(names) or not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', x) for x in names):
        raise ValueError('bad variable list')
    prime = int(next(stream))
    if not 2 < prime < 2**31:
        raise ValueError('finite field characteristic required')
    return names, prime, comments


def parse_poly(raw, positions, prime):
    raw = re.sub(r'\s+mod\s+' + str(prime) + r'\b', '', raw)
    raw = re.sub(r'\s+', '', raw)
    data = {}
    for token in re.findall(r'[+-]?[^+-]+', raw):
        coeff = -1 if token.startswith('-') else 1
        exp = [0] * len(positions)
        for factor in token.lstrip('+-').split('*'):
            if re.fullmatch(r'\d+(?:/\d+)?', factor):
                nums = factor.split('/')
                coeff = coeff * int(nums[0]) % prime
                if len(nums) == 2:
                    coeff = coeff * pow(int(nums[1]), -1, prime) % prime
            else:
                match = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)(?:\^(\d+))?', factor)
                if match is None or match[1] not in positions:
                    raise ValueError('bad polynomial factor')
                exp[positions[match[1]]] += int(match[2] or 1)
        exp = tuple(exp)
        data[exp] = (data.get(exp, 0) + coeff) % prime
    return {e: c for e, c in data.items() if c}


def append_input(path, lens, coeffs, exps, expected=None, original_sha=None):
    with open_text(path) as stream:
        names, prime, comments = header(stream)
        if expected is not None and (names, prime) != expected:
            raise ValueError('checkpoint field or ordered variables mismatch')
        if original_sha is not None:
            if not comments or not comments[0].startswith('# PARTIAL '):
                raise ValueError('resume input is not explicitly PARTIAL')
            if '# original_sha256=' + original_sha not in comments:
                raise ValueError('checkpoint original input SHA256 mismatch')
        positions = {x: i for i, x in enumerate(names)}
        pending = ''
        for line in stream:
            if line.startswith('#'):
                raise ValueError('unexpected comment within polynomial data')
            pieces = (pending + line).split(',')
            pending = pieces.pop()
            for raw in pieces:
                if not raw.strip():
                    continue
                poly = parse_poly(raw, positions, prime)
                if poly:
                    lens.append(len(poly))
                    for e, c in sorted(poly.items(), key=lambda z: (-sum(z[0]), tuple(reversed(z[0])))):
                        exps.extend(e)
                        coeffs.append(c)
        if pending.strip():
            poly = parse_poly(pending, positions, prime)
            if poly:
                lens.append(len(poly))
                for e, c in sorted(poly.items(), key=lambda z: (-sum(z[0]), tuple(reversed(z[0])))):
                    exps.extend(e)
                    coeffs.append(c)
    return names, prime


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('-f', '--input', required=True, help='unchanged original mathematical input')
    p.add_argument('-o', '--output', required=True, help='small status JSON; completed basis streams here')
    p.add_argument('--checkpoint', required=True, help='latest .gz PARTIAL snapshot')
    p.add_argument('--resume', help='previous .gz snapshot; always unioned with original input')
    p.add_argument('--checkpoint-seconds', type=float, default=300)
    p.add_argument('--checkpoint-max-mib', type=float, default=256, help='uncompressed snapshot size cap')
    p.add_argument('--stop-after-rounds', type=int, default=0)
    p.add_argument('--stop-after-seconds', type=float, default=0)
    p.add_argument('-t', '--threads', type=int, default=2)
    p.add_argument('--info', type=int, choices=[0, 1, 2], default=2)
    p.add_argument('--la', type=int, choices=[1, 2, 42, 44], default=2)
    p.add_argument('--max-pairs', type=int, default=0)
    p.add_argument('--hash-size', type=int, default=17)
    p.add_argument('--eliminate', type=int, default=0)
    p.add_argument('--no-reduce', action='store_true')
    a = p.parse_args()
    if not a.checkpoint.endswith('.gz'):
        p.error('--checkpoint must end in .gz')
    if min(a.checkpoint_seconds, a.stop_after_seconds, a.stop_after_rounds) < 0 or a.checkpoint_max_mib <= 0:
        p.error('checkpoint timing and cap must be nonnegative, with positive cap')
    with open(a.input, 'rb') as stream:
        original_sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    lens, coeffs, exps = array('i'), array('i'), array('i')
    names, prime = append_input(a.input, lens, coeffs, exps)
    if a.resume:
        append_input(a.resume, lens, coeffs, exps, (names, prime), original_sha)
    if not lens:
        p.error('no nonzero input generators')
    generators = len(lens)
    print(json.dumps({'stage': 'parsed', 'variables': len(names), 'generators': generators,
                      'terms': len(coeffs), 'prime': prime, 'original_sha256': original_sha,
                      'resume_union': bool(a.resume)}), flush=True)
    lib = C.CDLL(str(Path(__file__).with_name('libneogb-checkpoint.so')))
    libc = C.CDLL(None)
    I = C.c_int32
    PI = C.POINTER(I)
    config = lib.neogb_checkpoint_configure
    config.argtypes = [C.c_char_p, C.c_char_p, C.c_char_p, C.c_double, C.c_uint,
                       C.c_double, C.c_uint64]
    config.restype = I
    if config(os.fsencode(a.checkpoint), ','.join(names).encode(), original_sha.encode(),
              a.checkpoint_seconds, a.stop_after_rounds, a.stop_after_seconds,
              int(a.checkpoint_max_mib * 2**20)):
        raise RuntimeError('checkpoint configuration failed')
    f = lib.export_f4
    f.argtypes = [C.c_void_p, PI, C.POINTER(PI), C.POINTER(PI), C.POINTER(C.c_void_p),
                  PI, PI, C.c_void_p, C.c_uint32] + [I] * 12
    f.restype = C.c_int64
    bload, blens, bexps, bcoeffs = I(), PI(), PI(), C.c_void_p()
    larr = (I * len(lens)).from_buffer(lens)
    earr = (I * len(exps)).from_buffer(exps)
    carr = (I * len(coeffs)).from_buffer(coeffs)
    # The ctypes views own the array buffers. No parallel Python polynomial lists survive.
    del lens, exps, coeffs
    gc.collect()
    started = time.time()
    nterms = f(C.cast(libc.malloc, C.c_void_p), C.byref(bload), C.byref(blens),
               C.byref(bexps), C.byref(bcoeffs), larr, earr, carr, prime, 0,
               a.eliminate, len(names), generators, a.hash_size, a.threads,
               a.max_pairs, 0, a.la, not a.no_reduce, 0, a.info)
    partial = bool(lib.neogb_checkpoint_was_partial())
    lib.neogb_checkpoint_kept.restype = C.c_uint64
    lib.neogb_checkpoint_total.restype = C.c_uint64
    result = {'variables': names, 'prime': prime, 'status': 'PARTIAL' if partial else 'COMPLETE',
              'is_groebner_basis': not partial, 'diagnostic_only': True,
              'original_sha256': original_sha, 'seconds': time.time() - started,
              'checkpoint': a.checkpoint, 'checkpoint_write_failed': bool(lib.neogb_checkpoint_failed()),
              'linear_algebra': a.la, 'checkpoint_progress_subset': bool(lib.neogb_checkpoint_subset()),
              'checkpoint_generators_retained': int(lib.neogb_checkpoint_kept()),
              'checkpoint_generators_total': int(lib.neogb_checkpoint_total())}
    output = Path(a.output)
    temporary = output.with_name(output.name + '.tmp')
    if partial:
        if nterms != -2 or bload.value != 0:
            raise RuntimeError('partial export unexpectedly allocated result arrays')
        temporary.write_text(json.dumps(result))
    else:
        result['terms'] = int(nterms)
        result['basis_size'] = bload.value
        cptr = C.cast(bcoeffs, PI)
        offset, unit = 0, False
        with temporary.open('w') as stream:
            stream.write(json.dumps(result)[:-1] + ', "basis":[')
            for i in range(bload.value):
                if i:
                    stream.write(',')
                stream.write('[')
                for j in range(blens[i]):
                    if j:
                        stream.write(',')
                    k = offset + j
                    e = [int(bexps[k * len(names) + v]) for v in range(len(names))]
                    c = int(cptr[k]) % prime
                    stream.write(json.dumps({'coefficient': c, 'exponents': e}))
                    if blens[i] == 1 and c and not any(e):
                        unit = True
                stream.write(']')
                offset += blens[i]
            stream.write('], "unit_ideal":' + json.dumps(unit) + '}')
        result['unit_ideal'] = unit
        libc.free.argtypes = [C.c_void_p]
        for pointer in (blens, bexps, bcoeffs):
            libc.free(C.cast(pointer, C.c_void_p))
    os.replace(temporary, output)
    print(json.dumps({'stage': 'finished', **result}), flush=True)


if __name__ == '__main__':
    main()
