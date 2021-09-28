set -eu # exit on first failed command
set -x  # echo commands as they are executed

sbt docs/docsSite
git rm -rf --ignore-unmatch docs/latest
mkdir -p docs/latest
cp -R docs-project/target/docs-site docs/latest
git add docs/latest
git commit
