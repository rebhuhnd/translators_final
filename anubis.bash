## Named after the Egyptian god of the afterlife who judged souls.
## This is a bash version of the auto judge.
FAILED_TO_COMPILE=()
PASSED=()
FAILED=()

for i in testcases_final/*.in; do
	echo Testing $i ...
    cat "$i" | python hw6_compiler.py > temp.c #2>/dev/null

	if clang temp.c -o temp -w
	then

		if diff <( ./temp ) <( python "$i" )
		then
			echo $i PASSED
			PASSED+=($i)
		else
			echo $i FAILED: Different output.
			FAILED+=($i)
		fi
	else
		echo $i FAILED: Compiling
		FAILED_TO_COMPILE+=($i)
    fi
done

rm temp
rm temp.c

echo "SUMMARY:"
echo "PASSED:"
printf '%s\n' "${PASSED[@]}"

echo "FAILED TO COMPILE:"
printf '%s\n' "${FAILED_TO_COMPILE[@]}"

echo "FAILED, BUT COMPILED:"
printf '%s\n' "${FAILED[@]}"
