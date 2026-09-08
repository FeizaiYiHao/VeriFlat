#!/usr/bin/env bash
# Usage: ./module_times.sh [-n threads] [module::path]
set -euo pipefail
CURRENT_DIR="$(cd "$(dirname "$0")" && pwd)"
exec "$CURRENT_DIR/verification_times.sh" modules "$@"
