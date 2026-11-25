from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import tarfile

JOB = Path('/tmp/oec/pequalnp-pilot-76')
REPO = Path('/workspace/pequalnp-proofs')
ROOT = JOB / 'toolchain'
REPORT = JOB / 'conservative-cleanup-report.json'
report = dict(started=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              initial_disk_free=shutil.disk_usage(JOB).free, operations=[])


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save():
    REPORT.write_text(json.dumps(report, indent=2) + '\n')


def allocated(path):
    p = Path(path)
    if p.is_file():
        return p.stat().st_blocks * 512
    return sum(q.stat().st_blocks * 512 for q in p.rglob('*') if q.is_file())


save()
outside = REPO / 'lean/PEqualNP/Outside'
assert (outside / 'L_meta_2583.lean').is_file()
assert sum(p.is_file() for p in outside.iterdir()) == 1, 'Wait for root sparse checkout'
assert shutil.disk_usage(JOB).free > 200_000_000

# The cache executable is not part of the named proof/checklemma build closure.
cache = REPO / 'lean/.lake/packages/mathlib/.lake/build/bin/cache'
archive = JOB / 'cache-executable.zst'
assert cache.is_file() and not cache.is_symlink() and not archive.exists()
before = dict(path=str(cache), bytes=cache.stat().st_size,
              allocated=allocated(cache), sha256=digest(cache), mode=cache.stat().st_mode & 0o777)
command = ['zstd', '-T1', '-3', str(cache), '-o', str(archive)]
with (JOB / 'cleanup-cache-compress.log').open('w') as log:
    subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
    check_command = ['zstd', '-dc', str(archive)]
    proc = subprocess.Popen(check_command, stdout=subprocess.PIPE, stderr=log)
    actual = hashlib.file_digest(proc.stdout, 'sha256').hexdigest()
    assert proc.wait() == 0 and actual == before['sha256']
assert digest(cache) == before['sha256']
cache.unlink()
report['operations'].append(dict(action='compress_verified_remove_cache', original=before,
    archive=str(archive), archive_bytes=archive.stat().st_size, archive_sha256=digest(archive),
    commands=[command, check_command], roundtrip_verified=True,
    disk_free=shutil.disk_usage(JOB).free))
save()

# Preserve every source byte, relative path, and symlink in a compressed tar.
source = ROOT / 'src'
source_archive = JOB / 'toolchain-sources.tar.zst'
assert source.is_dir() and not source.is_symlink() and not source_archive.exists()
source_allocated = allocated(source)
members = {}
for p in sorted(source.rglob('*')):
    name = str(p.relative_to(ROOT))
    if p.is_symlink():
        members[name] = dict(kind='symlink', target=os.readlink(p))
    elif p.is_file():
        members[name] = dict(kind='file', bytes=p.stat().st_size, sha256=digest(p))
(JOB / 'toolchain-source-manifest.json').write_text(json.dumps(members, indent=2) + '\n')
tar_command = ['tar', '-C', str(ROOT), '-cf', '-', 'src']
zstd_command = ['zstd', '-T1', '-3', '-o', str(source_archive)]
with (JOB / 'cleanup-source-compress.log').open('w') as log:
    tar = subprocess.Popen(tar_command, stdout=subprocess.PIPE, stderr=log)
    zstd = subprocess.Popen(zstd_command, stdin=tar.stdout, stdout=log, stderr=subprocess.STDOUT)
    tar.stdout.close()
    assert zstd.wait() == 0 and tar.wait() == 0
    check_command = ['zstd', '-dc', str(source_archive)]
    proc = subprocess.Popen(check_command, stdout=subprocess.PIPE, stderr=log)
    seen = set()
    with tarfile.open(fileobj=proc.stdout, mode='r|') as tf:
        for item in tf:
            if item.isdir():
                continue
            assert item.name in members, item.name
            record = members[item.name]
            if record['kind'] == 'file':
                assert item.isfile() and item.size == record['bytes']
                assert hashlib.file_digest(tf.extractfile(item), 'sha256').hexdigest() == record['sha256']
            else:
                assert item.issym() and item.linkname == record['target']
            seen.add(item.name)
    assert proc.wait() == 0 and seen == set(members)
for name, record in members.items():
    p = ROOT / name
    if record['kind'] == 'file':
        assert p.is_file() and digest(p) == record['sha256']
    else:
        assert p.is_symlink() and os.readlink(p) == record['target']
shutil.rmtree(source)
report['operations'].append(dict(action='compress_verified_remove_toolchain_sources',
    original=str(source), original_allocated=source_allocated, members=len(members),
    archive=str(source_archive), archive_bytes=source_archive.stat().st_size,
    archive_sha256=digest(source_archive), commands=[tar_command, zstd_command, check_command],
    roundtrip_verified=True, disk_free=shutil.disk_usage(JOB).free))
save()

# Only the abandoned failed-mount experiment is cleaned. Its public source
# archives, all logs, and the useful SquashFS reader/tools remain untouched.
archives = [JOB / 'fuse-2.9.9.tar.gz', JOB / 'squashfuse-0.6.5.tar.gz']
source_recovery = []
for p in archives:
    assert p.is_file()
    with tarfile.open(p, 'r:gz') as tf:
        names = tf.getnames()
        assert names and any(n.endswith('/configure') for n in names)
    source_recovery.append(dict(path=str(p), bytes=p.stat().st_size, sha256=digest(p)))
logs = ['fuse-download.log', 'fuse-configure.log', 'fuse-build.log', 'fuse-install.log',
        'squashfuse-download.log', 'squashfuse-configure.log', 'squashfuse-build.log',
        'squashfuse-configure-proper.log', 'squashfuse-build-proper.log', 'toolchain-static-mount.log']
assert all((JOB / name).is_file() for name in logs)
with (JOB / 'cleanup-fuse-processes.log').open('w') as log:
    result = subprocess.run(['ps', '-eo', 'comm='], text=True, stdout=subprocess.PIPE,
                            stderr=log, check=True)
    log.write(result.stdout)
    assert not any(s.strip() in {'squashfuse', 'squashfuse_ll'} for s in result.stdout.splitlines())
for name in ['fuse-2.9.9', 'fuse-install', 'squashfuse-0.6.5']:
    p = JOB / name
    assert p.is_dir() and not p.is_symlink() and p.resolve().parent == JOB
    size = allocated(p)
    shutil.rmtree(p)
    report['operations'].append(dict(action='remove_failed_fuse_tree', path=str(p),
        allocated=size, source_recovery=source_recovery, retained_logs=logs,
        disk_free=shutil.disk_usage(JOB).free))
    save()

assert (JOB / 'toolchain-static.sqfs').is_file()
assert (JOB / 'optional-toolchain.tar.zst').is_file()
assert (JOB / 'squashfs-tools-4.7.5/squashfs-tools/unsquashfs').is_file()
report['finished'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
report['final_disk_free'] = shutil.disk_usage(JOB).free
save()
print(json.dumps(dict(status='verified_cleanup_complete', initial_disk_free=report['initial_disk_free'],
                      final_disk_free=report['final_disk_free'], operations=len(report['operations']))))
