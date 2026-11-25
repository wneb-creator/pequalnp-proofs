"""Small provenance, format, and rejection controls for lrat_restart."""
import gzip
import json
import tempfile
from pathlib import Path
from types import SimpleNamespace

import lrat_restart as restart
from lrat_pack import convert

ROOT = Path(__file__).parent


def expect_error(action, fragment):
    try:
        action()
    except ValueError as exc:
        assert fragment in str(exc), (fragment, str(exc))
    else:
        raise AssertionError('expected rejection: ' + fragment)


def main():
    with tempfile.TemporaryDirectory(prefix='restart-tests-', dir=ROOT) as name:
        work = Path(name)
        cnf = work / 'original.cnf'
        cnf.write_text('p cnf 3 4\n1 2 0\n-1 0\n-2 0\n3 -3 0\n')
        prefix = work / 'prefix.lrat.gz'
        with gzip.open(prefix, 'wb') as stream:
            stream.write(b'5 -1 0 2 0\n6 2 0 2 1 0\n6 d 5 0\n')
        resumed = work / 'resumed.blrat'
        with resumed.open('wb') as stream:
            restart.emit(stream, 6, [], [5, 3])
        cp = SimpleNamespace(cnf=cnf, prefix=prefix, output_cnf=work / 'checkpoint.cnf',
                             manifest=work / 'manifest.json', max_length=None, max_learned=None)
        restart.checkpoint(cp)
        manifest = json.loads(cp.manifest.read_text())
        assert manifest['learned_ids'] == [6]
        assert manifest['restart_initial_clauses'] == 5
        st = SimpleNamespace(cnf=cnf, prefix=prefix, checkpoint_cnf=cp.output_cnf,
                             manifest=cp.manifest, resumed=resumed, output=work / 'stitched.blrat')
        restart.stitch(st)
        packed = convert(cnf, st.output)
        known = convert(ROOT / 'chain.cnf', ROOT / 'chain.lrat')
        for key in ['tokens', 'words', 'keep_words', 'width', 'initial_clauses']:
            assert packed[key] == known[key], key
        assert packed['tokens'] == [4, 4, 0, 1, 3, 0, 5, 0, 4, 4, 2]
        assert packed['words'] == [11342721572]
        print('PASS gzip prefix, deletion, remapped learned input, binary resume, original-CNF packing')
        print('PASS exact match to previously kernel-checked packed chain control')

        initial = restart.read_cnf(cnf)
        bad = work / 'bad.lrat'
        bad.write_text('5 -1 0 -2 0\n')
        expect_error(lambda: restart.scan(bad, initial), 'RAT/negative')
        bad.write_text('5 2 0 1 0\n')
        expect_error(lambda: restart.scan(bad, initial), 'no RUP conflict')
        bad.write_text('5 -1 0 2 0\n5 d 5 0\n6 0 5 3 0\n')
        expect_error(lambda: restart.scan(bad, initial), 'unknown or deleted')
        bad.write_bytes(b'a\x80')
        expect_error(lambda: restart.scan(bad, initial), 'truncated')
        print('PASS RAT, invalid RUP, deleted-hint, and truncated-binary rejection')

        broken_manifest = work / 'broken-manifest.json'
        broken = dict(manifest)
        broken['prefix_sha256'] = '0' * 64
        broken_manifest.write_text(json.dumps(broken))
        st.manifest = broken_manifest
        st.output = work / 'hash-mismatch.blrat'
        expect_error(lambda: restart.stitch(st), 'source hash mismatch')
        assert not st.output.exists()
        print('PASS changed-prefix hash rejection')

        changed_cnf = work / 'changed-checkpoint.cnf'
        changed_cnf.write_text(cp.output_cnf.read_text().rsplit('2 0\n', 1)[0] + '1 0\n')
        broken = dict(manifest)
        broken['checkpoint_cnf_sha256'] = restart.digest(changed_cnf)
        broken_manifest.write_text(json.dumps(broken))
        st.checkpoint_cnf = changed_cnf
        st.output = work / 'changed-clause.blrat'
        expect_error(lambda: restart.stitch(st), 'learned clause content mismatch')
        assert not st.output.exists()
        print('PASS forged learned-clause content rejection even with updated manifest hash')

        st.manifest = cp.manifest
        st.checkpoint_cnf = cp.output_cnf
        unfinished = work / 'unfinished.lrat'
        unfinished.write_text('6 2 0 5 0\n')
        st.resumed = unfinished
        st.output = work / 'unfinished-output.blrat'
        expect_error(lambda: restart.stitch(st), 'completed empty-clause')
        assert not st.output.exists()
        print('PASS unfinished continuation rejection; no final output published')
    print('ALL RESTART CONTROLS PASSED')


if __name__ == '__main__':
    main()
