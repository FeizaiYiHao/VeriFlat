if [ "$BASH_VERSION" ]; then
  CURRENT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
else
  echo "Unknown shell; exiting."
  return 1
fi
FLAGS=""
for opt in "$@"; do
    echo $opt
    FLAGS+=" $opt"
done

echo $FLAGS

$CURRENT_DIR/verus/source/target-verus/release/verus $CURRENT_DIR/lib.rs $FLAGS
