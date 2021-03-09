set -eu # exit on first failed command

sbt doc
git rm -rf docs/scaladoc/snapshot
mkdir -p docs/scaladoc
cp -R core/target/scala-3.0.0-RC1/api docs/scaladoc/snapshot
git add docs/scaladoc/snapshot
git commit
