## A bash version of the auto judge.
TESTCASES_DIR=testcases_final
COMPILER=hw6_compiler.py

## Array of test cases that failed to compile.
FAILED_TO_COMPILE=()

## Array of test cases that passed.
PASSED=()

## Array of test cases that compiled
# but did not generate the same output.
FAILED=()

for i in $TESTCASES_DIR/*.in; do
	echo Testing $i ...
    cat "$i" | python $COMPILER > temp.c #2>/dev/null

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

## Removes temporary files

rm temp
rm temp.c

## Prints a summary.

echo "SUMMARY:"
echo "PASSED:"
printf '%s\n' "${PASSED[@]}"

echo "FAILED TO COMPILE:"
printf '%s\n' "${FAILED_TO_COMPILE[@]}"

echo "FAILED, BUT COMPILED:"
printf '%s\n' "${FAILED[@]}"
