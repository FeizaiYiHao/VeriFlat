CURRENT_DIR="$( cd "$( dirname "$0" )" >/dev/null 2>&1 && pwd )"
FLAGS=""
for opt in "$@"; do
    FLAGS+=" $opt"
done

$CURRENT_DIR/verus/source/target-verus/release/verus $CURRENT_DIR/src/lib.rs $FLAGS
