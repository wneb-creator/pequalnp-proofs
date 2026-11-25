from pathlib import Path
import gzip, hashlib, json, os, shutil, subprocess, sys, time

ROOT = Path('/tmp/oec/pequalnp-pilot-94')
STATE = ROOT / 'memory-cache-transferred'
PACKAGES = Path('/workspace/pequalnp-proofs/lean/.lake/packages')
STATE.mkdir(exist_ok=True)


def sha_file(path):
    with open(path, 'rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def worker():
    held = []
    links = []
    try:
        for line in sys.stdin:
            task = json.loads(line)
            if task.get('stop'):
                break
            results = []
            for item in task['artifacts']:
                path = Path(item['path'])
                assert path.is_relative_to(PACKAGES)
                assert '.lake/build/' in str(path.relative_to(PACKAGES))
                old_target = '/proc/' + str(item['holder_pid']) + '/fd/' + str(item['fd'])
                assert path.is_symlink() and os.readlink(path) == old_target
                fd = os.open(old_target, os.O_RDONLY | os.O_CLOEXEC)
                stat = os.fstat(fd)
                assert stat.st_size == item['bytes']
                assert sha_file('/proc/self/fd/' + str(fd)) == item['sha256']
                temporary = path.with_name(path.name + '.pilot94-transfer-' + str(os.getpid()))
                assert not temporary.exists() and not temporary.is_symlink()
                if item['disk']:
                    assert shutil.disk_usage(path.parent).free - item['bytes'] > 105 * 1024**2
                    with os.fdopen(os.dup(fd), 'rb') as source, temporary.open('xb') as out:
                        shutil.copyfileobj(source, out, 1024 * 1024)
                        out.flush()
                        os.fsync(out.fileno())
                    assert temporary.stat().st_size == item['bytes']
                    assert sha_file(temporary) == item['sha256']
                    os.chmod(temporary, stat.st_mode & 0o777)
                    os.utime(temporary, ns=(stat.st_atime_ns, stat.st_mtime_ns))
                    os.replace(temporary, path)
                    os.close(fd)
                    results.append({**item, 'storage': 'disk', 'new_holder_pid': None, 'new_fd': None})
                else:
                    target = '/proc/' + str(os.getpid()) + '/fd/' + str(fd)
                    temporary.symlink_to(target)
                    os.replace(temporary, path)
                    held.append(fd)
                    links.append((path, target))
                    results.append({**item, 'storage': 'sealed-original-inode', 'new_holder_pid': os.getpid(), 'new_fd': fd})
            with gzip.open(STATE / 'artifacts.jsonl.gz', 'at', compresslevel=6) as out:
                for result in results:
                    out.write(json.dumps(result) + '\n')
            print(json.dumps({'ok': True, 'artifacts': len(results), 'fds': len(held), 'pid': os.getpid()}), flush=True)
    except BaseException as error:
        print(json.dumps({'ok': False, 'error': repr(error)}), flush=True)
        # Keep successfully transferred inodes alive for diagnosis/recovery.
        while not (STATE / 'STOP').exists():
            time.sleep(1)
        raise
    finally:
        for path, target in links:
            if path.is_symlink() and os.readlink(path) == target:
                path.unlink()
        for fd in held:
            os.close(fd)


def main():
    rows = [json.loads(line) for line in (ROOT / 'memory-cache/artifacts.jsonl').read_text().splitlines()]
    items = []
    for row in rows:
        items.extend({**artifact, 'module': row['module'], 'official_source_hash': row['official_source_hash']} for artifact in row['artifacts'])
    assert len(items) == 88125
    budget = min(330 * 1024**2, shutil.disk_usage(ROOT).free - 120 * 1024**2)
    assert budget > 0
    selected = set()
    disk_bytes = 0
    for item in sorted(items, key=lambda x: x['bytes'], reverse=True):
        if disk_bytes + item['bytes'] <= budget:
            selected.add(item['path'])
            disk_bytes += item['bytes']
    for item in items:
        item['disk'] = item['path'] in selected
    (STATE / 'plan.json').write_text(json.dumps({'artifacts': len(items), 'disk_artifacts': len(selected), 'disk_bytes': disk_bytes, 'budget': budget}, indent=2) + '\n')
    workers = []
    count = 0
    failure = None
    started = time.time()
    diagnostics = (STATE / 'diagnostics.log').open('a')

    def save(status):
        temporary = STATE / 'status.next.json'
        temporary.write_text(json.dumps({'status': status, 'pid': os.getpid(), 'holders': [p.pid for p in workers], 'completed': count, 'total': len(items), 'disk_bytes': disk_bytes, 'elapsed_seconds': time.time() - started, 'error': failure}, indent=2) + '\n')
        temporary.replace(STATE / 'status.json')

    try:
        save('transferring')
        for start in range(0, len(items), 9000):
            proc = subprocess.Popen([sys.executable, __file__, 'worker'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=diagnostics, text=True, bufsize=1)
            workers.append(proc)
            chunk = items[start:start + 9000]
            proc.stdin.write(json.dumps({'artifacts': chunk}) + '\n')
            proc.stdin.flush()
            response = proc.stdout.readline()
            assert response, 'holder exited before response'
            answer = json.loads(response)
            assert answer['ok'], answer
            count += answer['artifacts']
            save('transferring')
            print(json.dumps({'completed': count, 'total': len(items), 'elapsed_seconds': time.time() - started}), flush=True)
        assert count == len(items)
        save('ready')
        print('TRANSFER_READY_OLD_HOLDERS_STILL_ALIVE', flush=True)
    except BaseException as error:
        failure = repr(error)
        save('incomplete')
        print('TRANSFER_INCOMPLETE ' + failure, flush=True)
    finally:
        while not (STATE / 'STOP').exists():
            if any(proc.poll() is not None for proc in workers):
                failure = 'A new holder exited'
                save('holder_failed')
                # Never close remaining holders automatically on another failure.
            time.sleep(2)
        for proc in workers:
            if proc.poll() is None:
                proc.stdin.write('{"stop":true}\n')
                proc.stdin.flush()
        for proc in workers:
            proc.wait()
        save('stopped')
        diagnostics.close()


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'worker':
        worker()
    else:
        main()
