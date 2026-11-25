import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import time


DECODER = '''import Mathlib.Data.List.Basic

namespace PEqualNP.Outside.L_meta_2373.WitnessCodec

def copyBytes (distance : Nat) : Nat → Nat → Nat → Nat
  | 0, _, out => out
  | remaining + 1, count, out =>
    let byte := (out >>> (8 * (count - distance))) &&& 255
    copyBytes distance remaining (count + 1) (out ||| (byte <<< (8 * count)))

def decode : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, count, out => (count, out)
  | fuel + 1, packed, count, out =>
    let header := packed &&& 255
    if header < 128 then
      let size := header + 1
      let bytes := (packed >>> 8) &&& ((1 <<< (8 * size)) - 1)
      decode fuel (packed >>> (8 * (size + 1))) (count + size)
        (out ||| (bytes <<< (8 * count)))
    else
      let size := header - 128 + 3
      let distance := (packed >>> 8) &&& 65535
      decode fuel (packed >>> 24) (count + size) (copyBytes distance size count out)

def decodeItem (item : Nat × Nat) : Nat × Nat := decode item.1 item.2 0 0

end PEqualNP.Outside.L_meta_2373.WitnessCodec
'''


def encode(data):
    packed = bytearray()
    commands = 0
    candidates = defaultdict(list)
    literals = bytearray()

    def flush():
        nonlocal commands
        if literals:
            packed.append(len(literals) - 1)
            packed.extend(literals)
            literals.clear()
            commands += 1

    i = 0
    while i < len(data):
        best, distance = 0, 0
        key = data[i:i+3]
        if len(key) == 3:
            for position in reversed(candidates[key][-64:]):
                dist = i - position
                if dist > 65535:
                    break
                size = 3
                while size < 130 and i + size < len(data) and data[position+size] == data[i+size]:
                    size += 1
                if size > best:
                    best, distance = size, dist
        size = best if best >= 4 else 1
        if size > 1:
            flush()
            packed.extend((128 + size - 3, distance & 255, distance >> 8))
            commands += 1
        else:
            literals.append(data[i])
            if len(literals) == 128:
                flush()
        for position in range(i, i + size):
            candidates[data[position:position+3]].append(position)
        i += size
    flush()
    return commands, bytes(packed)


def decode(commands, packed):
    output = bytearray()
    cursor = 0
    for _ in range(commands):
        header = packed[cursor]
        cursor += 1
        if header < 128:
            size = header + 1
            output.extend(packed[cursor:cursor+size])
            cursor += size
        else:
            size = header - 128 + 3
            distance = packed[cursor] + 256 * packed[cursor+1]
            cursor += 2
            for _ in range(size):
                output.append(output[-distance])
    assert cursor == len(packed)
    return bytes(output)


def literal(item):
    commands, packed = item
    return '(' + str(commands) + ',0x' + packed[::-1].hex().lstrip('0') + ')'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    data = args.input.read_bytes()
    assert hashlib.sha256(data).hexdigest() in ['c539de6a9c37303c1c71a39fcc77010ed72641a74a33afc767d671e89ad0769d', 'c99a645e1337e3ea0a04cda950552dfad549fd5c8e99be53449eff465c4f7650']
    (args.output/'WitnessDecoder.lean').write_text(DECODER)
    results = []
    for chunk_size in [512, 2048, 8192, 32768]:
        start = time.monotonic()
        raw = [data[i:i+chunk_size] for i in range(0,len(data),chunk_size)]
        encoded = [encode(chunk) for chunk in raw]
        for chunk, item in zip(raw,encoded):
            assert decode(*item) == chunk
        payload = '[' + ','.join(literal(item) for item in encoded) + ']'
        source = 'import WitnessDecoder\n\nnamespace PEqualNP.Outside.L_meta_2373.WitnessCodec\n\ndef payload : List (Nat × Nat) := ' + payload + '\n\nend PEqualNP.Outside.L_meta_2373.WitnessCodec\n'
        (args.output/f'Payload{chunk_size}.lean').write_text(source)
        results.append(dict(chunk_size=chunk_size,chunks=len(raw),commands=sum(x[0] for x in encoded),
                            compressed_bytes=sum(len(x[1]) for x in encoded),payload_source_bytes=len(source.encode()),
                            decoder_source_bytes=len(DECODER.encode()),seconds=time.monotonic()-start))
        if chunk_size in [512,2048]:
            for sample_size in [2048,16384]:
                sample_raw = raw[:sample_size//chunk_size]
                sample_encoded = encoded[:sample_size//chunk_size]
                source='import WitnessDecoder\n\nnamespace PEqualNP.Outside.L_meta_2373.WitnessCodec\n\n'
                source+='def actual : List (Nat × Nat) := ['+','.join(literal(x) for x in sample_encoded)+']\n'
                source+='def expected : List (Nat × Nat) := ['+','.join('('+str(len(x))+',0x'+x[::-1].hex().lstrip('0')+')' for x in sample_raw)+']\n'
                source+='\nset_option maxRecDepth 65536 in\nset_option maxHeartbeats 0 in\nlemma decoded : actual.map decodeItem = expected := by\n  decide +kernel\n\nend PEqualNP.Outside.L_meta_2373.WitnessCodec\n'
                (args.output/f'Benchmark{chunk_size}_{sample_size}.lean').write_text(source)
        print(json.dumps(results[-1]),flush=True)
    (args.output/'compression-report.json').write_text(json.dumps(dict(input=str(args.input),input_bytes=len(data),
        input_sha256=hashlib.sha256(data).hexdigest(),results=results,
        scope='Storage prototype only; source stream omits node/cut boundaries and profile/rectangle certificates.'),indent=2)+'\n')


if __name__=='__main__':main()
