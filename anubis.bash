## Named after the Egyptian god of the afterlife who judged souls.
## This is a bash version of the auto judge.

for i in testcases_final/*.in; do
    cat "$i" | python hw6_compiler.py > temp.c 2>/dev/null
    clang temp.c -o temp
    diff <( ./temp ) <( python "$i" ) && echo $i PASSED
done

rm temp
rm temp.c
