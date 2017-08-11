#! /bin/sh

fail() {
  echo "failure to compile: " $1
  exit 1
}

cargo build
echo
for file in language/tests/*.cf
do
  echo "compiling $file"
  cargo run -q -- --no-output "$file" || fail $?
done
