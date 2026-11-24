#!/usr/bin/env bash
set -u
pnp_environment=$1
pnp_workdir=$2
shift 2
source "$pnp_environment" && cd "$pnp_workdir" && exec "$@"
