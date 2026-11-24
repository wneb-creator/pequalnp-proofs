import pathlib
import shutil


class ClauseCount:
    def __init__(self):
        self.count = 0

    def __len__(self):
        return self.count


def streaming_class(base_class, body_path):
    """Preserve base var/one logic while streaming exactly the same clauses."""
    class StreamingCNF(base_class):
        def __init__(self):
            self.n = 0
            self.cs = ClauseCount()
            self._body_path = pathlib.Path(body_path)
            self._body = self._body_path.open('x+b', buffering=1048576)
            self._body_bytes = 0

        def add(self, *literals):
            encoded = (' '.join(map(str, literals))+' 0\n').encode('ascii')
            self._body.write(encoded)
            self._body_bytes += len(encoded)
            self.cs.count += 1

        def save(self, path):
            target = pathlib.Path(path)
            temporary = target.with_name(target.name+'.part')
            if target.exists() or temporary.exists():
                raise FileExistsError('Refusing to overwrite an existing CNF artifact')
            header = f'p cnf {self.n} {len(self.cs)}\n'.encode('ascii')
            self._body.flush()
            self._body.seek(0)
            with temporary.open('xb', buffering=1048576) as output:
                output.write(header)
                shutil.copyfileobj(self._body, output, length=1048576)
            assert temporary.stat().st_size == len(header)+self._body_bytes
            self._body.close()
            temporary.replace(target)
            self._body_path.unlink()

    return StreamingCNF
