import argparse
import importlib.util
import json
import math
import os
import shutil
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')
spec = importlib.util.spec_from_file_location('reviewed_fallback', BASE / 'resource-wrapper/shared-library-fallback/storage_phase.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

parser = argparse.ArgumentParser()
parser.add_argument('--config', required=True)
parser.add_argument('--core-config', required=True)
parser.add_argument('--retirements', nargs='*', default=[])
parser.add_argument('--snapshot-allowance', type=int, default=0)
parser.add_argument('--future-smoke-archive', type=int, default=2097152)
args = parser.parse_args()
config = json.loads(Path(args.config).read_text())
core_config = json.loads(Path(args.core_config).read_text())
storage = module.Storage(config)
records = json.loads(storage.prepared.read_text())['files']
build = [records[str(path)] for path in storage.candidates()]
ram, total, evacuated = storage.ram_plan()
plan = {'status': 'planned', 'build': build, 'ram': ram,
        'pinned_before': total, 'evacuated_bytes': evacuated}
journal_estimate = len(json.dumps(plan, separators=(',', ':')).encode()) + 4096
round_block = lambda size: math.ceil(size / 4096) * 4096
build_allocated = sum(Path(row['path']).stat().st_blocks * 512 for row in build)
ram_allocated = sum(round_block(row['size']) for row in ram)
free = shutil.disk_usage(storage.state).free
retire_allocated = sum(Path(p).stat().st_blocks * 512 for p in args.retirements)
old_journal_allocation = storage.journal.stat().st_blocks * 512 if storage.journal.exists() else 0
core_state = Path(core_config['state_dir'])
core = json.loads((core_state / 'prepared.json').read_text())
core_journal = core_state / 'transaction.json'
old_core_journal_allocation = core_journal.stat().st_blocks * 512 if core_journal.exists() else 0
core_journal_estimate = len(json.dumps(dict(core, status='entered'), indent=2).encode()) + 1 + 4096
projected_idle = free + retire_allocated - args.snapshot_allowance
verify_exact_blocks = (projected_idle + build_allocated - ram_allocated
                       - round_block(journal_estimate) + old_journal_allocation
                       - round_block(core_journal_estimate) + old_core_journal_allocation)
result = {'status': 'readonly_projection', 'disk_free_now': free,
          'retirement_allocation': retire_allocated, 'snapshot_allowance': args.snapshot_allowance,
          'projected_idle': projected_idle, 'build_files': len(build),
          'build_allocated': build_allocated, 'ram_files': len(ram),
          'ram_allocated': ram_allocated, 'evacuated_bytes': evacuated,
          'base_journal_estimate': journal_estimate, 'core_journal_estimate': core_journal_estimate,
          'entry_guard': 3 * journal_estimate + 16 * 1024 * 1024,
          'verify_blocks_projection': verify_exact_blocks,
          'verify_conservative_after_4MiB_metadata': verify_exact_blocks - 4 * 1024 * 1024,
          'future_smoke_archive_allowance': args.future_smoke_archive,
          'after_smoke_verify_conservative': verify_exact_blocks - 4 * 1024 * 1024 - args.future_smoke_archive,
          'reserve_bytes': config['disk_reserve_bytes'],
          'margin_after_4MiB_metadata': verify_exact_blocks - 4 * 1024 * 1024 - config['disk_reserve_bytes'],
          'after_smoke_margin': verify_exact_blocks - 4 * 1024 * 1024 - args.future_smoke_archive - config['disk_reserve_bytes'],
          'raw_pinned_after_core': total - evacuated - core['bytes'],
          'core_pack_disk_bytes': (core_state / 'excluded.zstpack').stat().st_size,
          'core_holder_retirement_required': True,
          'pending_backups': sum('pack' not in row for row in build)}
print(json.dumps(result, indent=2), flush=True)
