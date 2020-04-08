#!/usr/bin/env bash

# rm -rf */
touch __init__.py

wget -nc -nv -O wabt.tgz -c https://github.com/WebAssembly/wabt/releases/download/1.0.12/wabt-1.0.12-linux.tar.gz
wget -nc -nv -O spec.zip -c https://github.com/WebAssembly/spec/archive/v1.1.zip

yes | unzip -q -j spec.zip 'spec-*/test/core/*' -d .
rm run.py README.md 
rm spec.zip

tar --wildcards --strip=1 -xf wabt.tgz 'wabt-*/wast2json'
rm wabt.tgz

mkdir skipped_tests
while read skip; do
    mv $skip.wast skipped_tests/
done < skipped_test_sets

for x in *"-"*.wast; do
  mv -- "$x" "${x//-/_}"
done

ls *.wast | sed 's/\.wast//g' > modules.txt

cores=$(python -c "import multiprocessing; print(max(multiprocessing.cpu_count() - 2, 1))")

cat > gen.sh << EOF
module=\$1
echo "Preparing \$module"
mkdir _\$module
touch _\$module/__init__.py
./wast2json --debug-names \$module.wast -o _\$module/\$module.json
mv \$module.wast _\$module/
python3 json2mc.py _\$module/\$module.json | black --quiet --fast - > _\$module/test_\$module.py
EOF

chmod +x gen.sh
cat modules.txt | xargs -n1 -P"$cores" ./gen.sh
rm gen.sh

mv test_callbacks.skip test_callbacks.py

exit 0
