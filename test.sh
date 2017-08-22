#! /bin/sh

fail() {
  echo "failure to compile '$1': " $2
  exit 1
}

succeed() {
  echo "accidentally compiled '$1' successfully"
}

cargo build || exit
echo
echo "running succeed tests"
for file in language/succeed-tests/*.cf
do
  echo "compiling $file"
  cargo run -q -- "$file" || fail "$file" $?
done

echo
echo "running fail tests"
for file in language/fail-tests/*.cf
do
  echo "compiling $file"
  cargo run -q -- --no-run "$file" && succeed "$file"
done
