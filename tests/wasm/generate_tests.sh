#!/usr/bin/env bash

rm -rf */
touch __init__.py

if ! [ -x "$(command -v wast2json)" ]; then
  wget -nc -nv -O wabt.tgz -c https://github.com/WebAssembly/wabt/releases/download/1.0.12/wabt-1.0.12-linux.tar.gz
  tar --wildcards --strip=1 -xf wabt.tgz 'wabt-*/wast2json'
  rm wabt.tgz
else
  cp "$(command -v wast2json)" .
fi

echo "Downloading spec tests"
wget -nc -nv -O spec.zip -c https://github.com/WebAssembly/spec/archive/v1.1.zip

echo "Unzipping spec tests"
timeout 3m bash -c "yes | unzip -q -j spec.zip 'spec-*/test/core/*' -d ."
rm run.py README.md 
rm spec.zip

echo "Skipping skipped tests"
mkdir skipped_tests
while read skip; do
    mv $skip.wast skipped_tests/
done < skipped_test_sets

echo "Renaming WAST Files"
for x in *"-"*.wast; do
  mv -- "$x" "${x//-/_}"
done

echo "Creating module list"
ls *.wast | sed 's/\.wast//g' > modules.txt

echo "Counting cores"
cores=$(python -c "import multiprocessing; print(max(multiprocessing.cpu_count() - 2, 1))")

echo "Running on $cores cores"
cat > gen.sh << EOF
module=\$1
echo "Preparing \$module"
mkdir _\$module
touch _\$module/__init__.py
./wast2json --debug-names \$module.wast -o _\$module/\$module.json
mv \$module.wast _\$module/
python3 json2mc.py _\$module/\$module.json | black --quiet --fast - > _\$module/test_\$module.py
EOF

echo "Wrote script file"
chmod +x gen.sh
cat modules.txt | xargs -n1 -P"$cores" ./gen.sh
rm gen.sh

mv test_callbacks.skip test_callbacks.py
echo "Generation complete!"

exit 0