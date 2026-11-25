#!/usr/bin/env python3
"""Inherit the checker's names-only sanitized environment without capturing values."""
import os
import re
import sys

for name in list(os.environ):
    if re.match(r'^(LAKE($|_)|LEAN_|ELAN_TOOLCHAIN$)', name):
        del os.environ[name]
os.environ['LAKE_ARTIFACT_CACHE'] = 'false'
os.execv(sys.executable, [sys.executable, '-B', *sys.argv[1:]])
