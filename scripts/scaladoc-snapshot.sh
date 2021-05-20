set -eu # exit on first failed command

sbt doc
git rm -rf docs/scaladoc/snapshot
mkdir -p docs/scaladoc
cp -R core/target/scala-3.0.0/api docs/scaladoc/snapshot

# Edit stylesheet to use a font that correctly renders Unicode boxes (box-drawing characters).
# TODO: Is there a better way to override the font used for code blocks?
ed docs/scaladoc/snapshot/styles/scalastyle.css << END
/--mono-font: "Fira Code"/
s/--mono-font: "Fira Code"/--mono-font: "Menlo"/
wq
END

git add docs/scaladoc/snapshot
git commit
