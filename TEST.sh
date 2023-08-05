#!/usr/bin/env bash

# Emit an error if undefined variable is used.
set -u

shopt -s nullglob

# Option flags.
declare FORCE_COLOR_OUTPUT=""
declare RUN_EXAMPLES_TESTS="true"
declare RUN_COMPILER_TESTS="true"
declare RUN_INTERACTIVE_MODE_TESTS="true"
declare RUN_HARPOON_MODE_TESTS="true"
declare PRINT_HARPOON_OUTPUT_ON_FAILURE=""
declare RESET_OUT_FILES=""
declare STOP_ON_FAILURE=""

declare -a BELUGA_FLAGS=()

declare -r ROOTDIR=${ROOTDIR:-$(pwd)}
declare -r TEMPDIR=${TEMPDIR:-$(mktemp -d)}
declare -r BUILDPATH=${BUILDPATH:-"${ROOTDIR}/_build/install/default/bin"}
declare SKIP_RSYNC=0

declare -r BELUGA=${BELUGA:-"${BUILDPATH}/beluga"}
declare -r HARPOON=${HARPOON:-"${BUILDPATH}/harpoon"}
declare -r REPLAY=${REPLAY:-"${BUILDPATH}/replay"}

declare -r TESTROOTDIR=${TESTROOTDIR:-"./t"}
declare -r TESTDIR=${TESTDIR:-"${TESTROOTDIR}/code"}
declare -r EXAMPLEDIR=${EXAMPLEDIR:-"./examples"}
declare -r INTERACTIVE_TESTDIR=${INTERACTIVE_TESTDIR:-"${TESTROOTDIR}/interactive"}
declare -r HARPOON_TESTDIR=${HARPOON_TESTDIR:-"${TESTROOTDIR}/harpoon"}

declare -i TIMEOUT=${TIMEOUT:-10}

function rsync_test_artifacts {
    rsync -ak "${ROOTDIR}/.admissible-fail" "${TEMPDIR}/.admissible-fail"
    rsync -ak --chmod=Fa+w "${ROOTDIR}/${TESTROOTDIR}/" "${TEMPDIR}/${TESTROOTDIR}"
    rsync -ak "${ROOTDIR}/${EXAMPLEDIR}/" "${TEMPDIR}/${EXAMPLEDIR}"
}

declare -i TEST_RESULT_TOTAL=0
declare -i TEST_RESULT_SUCCESS=0
declare -i TEST_RESULT_TIMEOUT=0
declare -i TEST_RESULT_ADMISSIBLE=0
declare -i TEST_RESULT_FAIL=0
declare -i TEST_RESULT_LEXER_FAIL=0
declare -i TEST_RESULT_REPLAY_FAIL=0
declare -i TEST_RESULT_HARPOON_FAIL=0

declare C_START=""
declare C_ADMISSIBLE=""
declare C_OK=""
declare C_TIMEOUT=""
declare C_FAIL=""
declare C_LEX_FAIL=""
declare C_ADDED=""
declare C_REMOVED=""
declare C_END=""

function main {
    cd "${ROOTDIR}"
    parse_opts "$@"
    if [[ -t 1 || -n "${FORCE_COLOR_OUTPUT}" ]]; then
        set_colors
    fi
    print_paths
    if [ ${SKIP_RSYNC} -eq 1 ]; then
        do_testing
    else
        rsync_test_artifacts
        cd "${TEMPDIR}"
        echo "${TEMPDIR}"
        do_testing
        cd "${ROOTDIR}"
        echo "${TEMPDIR}"
    fi
}

function parse_opts {
    while [ "$#" -gt 0 ]; do
        case "$1" in
            -h|--help)
                usage
                exit 0
                ;;
            -c|--colour|--color)
                FORCE_COLOR_OUTPUT="true"
                ;;
            --reset)
                SKIP_RSYNC=1
                RESET_OUT_FILES="true"
                ;;
            --printharpoon)
                PRINT_HARPOON_OUTPUT_ON_FAILURE="true"
                STOP_ON_FAILURE="true"
                ;;
            --stop)
                STOP_ON_FAILURE="true"
                ;;
            --)
                shift
                break
                ;;
            "")
                break
                ;;
            *)
                echo "Unrecognized option $1."
                echo "Make sure to write -- before any argument that should be passed to Beluga."
                exit 2
                ;;
        esac
        shift
    done

    BELUGA_FLAGS=("$@")
}

function do_testing {
    local is_failed=0 file_path
    # Limit runtime of each test case, in seconds.
    ulimit -t "${TIMEOUT}"

    if [[ -n "${RUN_EXAMPLES_TESTS}" ]]; then
        echo "===== EXAMPLES ====="

        for file_path in $(find_compiler_tests_in "${EXAMPLEDIR}"); do
            start_test_case "${file_path}"

            check_example_test_case "${file_path}"
        done
    fi

    if [[ -n "${RUN_COMPILER_TESTS}" ]]; then
        echo "===== COMPILER TESTS ====="

        for file_path in $(find_compiler_tests_in "${TESTDIR}"); do
            start_test_case "${file_path}"

            check_compiler_test_case "${file_path}"
        done
    fi

    if [[ -n "${RUN_INTERACTIVE_MODE_TESTS}" ]]; then
        echo "===== INTERACTIVE MODE TESTS ====="

        for file_path in $(find "${INTERACTIVE_TESTDIR}" -type f | sort -n); do
            start_test_case "${file_path}"

            check_interactive "${file_path}"
        done
    fi

    if [[ -n "${RUN_HARPOON_MODE_TESTS}" ]]; then
        echo "===== HARPOON MODE TESTS ====="

        for file_path in $(find "${HARPOON_TESTDIR}" -type f -name "*.input" | sort -n); do
            start_test_case "${file_path}"

            check_harpoon "${file_path}"
        done
    fi

    echo
    echo "Successes: ${TEST_RESULT_SUCCESS}"
    echo "Failures: ${TEST_RESULT_FAIL}"
    echo "Lexer failures: ${TEST_RESULT_LEXER_FAIL}"
    echo "Admissible failures: ${TEST_RESULT_ADMISSIBLE}"
    echo "Timeouts: ${TEST_RESULT_TIMEOUT}"
    echo "Interactive mode failures: ${TEST_RESULT_REPLAY_FAIL}"
    echo "Harpoon mode failures: ${TEST_RESULT_HARPOON_FAIL}"
    echo "Total: ${TEST_RESULT_TOTAL}"
    echo
    times

    (( is_failed=TEST_RESULT_FAIL + TEST_RESULT_TIMEOUT + TEST_RESULT_LEXER_FAIL + TEST_RESULT_REPLAY_FAIL + TEST_RESULT_HARPOON_FAIL ))
    # If not all tests succeeded then exit with non-zero status.
    # double-negate the failure count to get 0 if it was zero, and
    # 1 if it was nonzero.
    exit $(( ! ! is_failed ))
}

function check_example_test_case {
    # Example test cases never have corresponding output files
    local -r file_path=$1

    local output output_file exit_code cmp_output diff_code

    # ${...[@]+${...[@]}} is a workaround for bash < 4.4
    # In bash < 4.4, array without an item is considered as an undefined variable.
    output_file="$(mktemp)"
    "${BELUGA}" +test "${BELUGA_FLAGS[@]+${BELUGA_FLAGS[@]}}" "${file_path}" >>"${output_file}" 2>&1
    exit_code=$?

    if [ "${exit_code}" -eq 152 ]; then
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE TIMEOUT${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
            (( TEST_RESULT_TIMEOUT+=1 ))
            stop_on_failure
        fi
    elif [ "${exit_code}" -eq 0 ]; then
        echo -e "${C_OK}OK${C_END}"
        (( TEST_RESULT_SUCCESS+=1 ))
    else
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_FAIL}FAIL${C_END}"
            (( TEST_RESULT_FAIL+=1 ))

            echo "${output}"

            stop_on_failure
        fi
    fi
}

function check_compiler_test_case {
    local -r file_path=$1

    local output output_file exit_code cmp_output diff_code out_file_exists

    # ${...[@]+${...[@]}} is a workaround for bash < 4.4
    # In bash < 4.4, array without an item is considered as an undefined variable.
    output_file="$(mktemp)"
    "${BELUGA}" +test "${BELUGA_FLAGS[@]+${BELUGA_FLAGS[@]}}" "${file_path}" >>"${output_file}" 2>&1
    exit_code=$?

    if [ "${exit_code}" -eq 152 ]; then
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE TIMEOUT${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
            (( TEST_RESULT_TIMEOUT+=1 ))
            stop_on_failure
        fi
    elif [[ ${exit_code} -eq 0 ]]; then
        if [ ! -f "${file_path}.out" ]; then
            echo -e "${C_OK}OK${C_END}"
            (( TEST_RESULT_SUCCESS+=1 ))
        else
            if grep -q "${file_path}" .admissible-fail; then
                echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
                (( TEST_RESULT_ADMISSIBLE+=1 ))
            else
                echo -e "${C_FAIL}FAIL${C_END}"
                (( TEST_RESULT_FAIL+=1 ))

                if [[ -f "${file_path}.out" ]]; then
                    diff --color --unified=3 "${file_path}.out" "${output_file}"
                else
                    cat "${output_file}"
                fi

                stop_on_failure
            fi
        fi
    else
        if [ -f "${file_path}.out" ]; then
            if cmp -s "${file_path}.out" "${output_file}"; then
                echo -e "${C_OK}OK${C_END}"
                (( TEST_RESULT_SUCCESS+=1 ))
            else
                if grep -q "${file_path}" .admissible-fail; then
                    echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
                    (( TEST_RESULT_ADMISSIBLE+=1 ))
                else
                    echo -e "${C_FAIL}FAIL${C_END}"
                    (( TEST_RESULT_FAIL+=1 ))

                    diff --color --unified=3 "${file_path}.out" "${output_file}"

                    stop_on_failure
                fi
            fi
        else
            if grep -q "${file_path}" .admissible-fail; then
                echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
                (( TEST_RESULT_ADMISSIBLE+=1 ))
            else
                echo -e "${C_FAIL}FAIL${C_END}"
                (( TEST_RESULT_FAIL+=1 ))

                cat "${output_file}"

                stop_on_failure
            fi
        fi
    fi

    if [[ -n "${RESET_OUT_FILES}" && -f "${file_path}.out" ]]; then
        cat "${output_file}" > "${file_path}.out"
    fi
}

function check_interactive {
    local -r file_path=$1

    local output exit_code

    output=$("${REPLAY}" "${BELUGA}" "${file_path}" 2>&1)
    exit_code=$?

    if [ "${exit_code}" -eq 152 ]; then
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE TIMEOUT${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
            (( TEST_RESULT_TIMEOUT+=1 ))
            stop_on_failure
        fi
    elif [ "${exit_code}" -eq 0 ]; then
        echo -e "${C_OK}OK${C_END}"
        (( TEST_RESULT_SUCCESS+=1 ))
    else
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_FAIL}FAIL${C_END}"
            (( TEST_RESULT_FAIL+=1 ))
            echo "${output}"

            stop_on_failure
        fi
    fi
}

function check_harpoon {
    local -r file_path=$1

    local output exit_code sig

    # Read the first line in the file at "${file_path}"
    sig=$(sed -n '1p' "${file_path}")

    output=$("${HARPOON}" --sig "${sig}" --test "${file_path}" --test-start 2 --no-save-back --stop 2>&1)
    exit_code=$?

    if [ "${exit_code}" -eq 152 ]; then
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE TIMEOUT${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
            (( TEST_RESULT_TIMEOUT+=1 ))
            stop_on_failure
        fi
    elif [ ${exit_code} -eq 0 ]; then
        echo -e "${C_OK}OK${C_END}"
        (( TEST_RESULT_SUCCESS+=1 ))
    else
        if grep -q "${file_path}" .admissible-fail; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_FAIL}FAIL${C_END}"
            (( TEST_RESULT_HARPOON_FAIL+=1 ))
            print_harpoon_output_on_failure "${output}"
            stop_on_failure
        fi
    fi
}

function start_test_case {
    local -r file_path=$1

    (( TEST_RESULT_TOTAL+=1 ))
    echo -ne "${C_START}**${C_END} TEST ${TEST_RESULT_TOTAL}: ${file_path} ... "
}

function print_harpoon_output_on_failure {
    local -r output=$1

    if [ -n "${PRINT_HARPOON_OUTPUT_ON_FAILURE}" ]; then
        echo "${output}"
    fi
}

function stop_on_failure {
    if [ -n "${STOP_ON_FAILURE}" ]; then
        exit 1
    fi
}

function find_compiler_tests_in {
    local -a tests

    for dir in $(find "$1" -type d); do
        tests=("${dir}/"*.cfg)
        if [ "${#tests[@]}" -eq 0 ]; then
            tests=("${dir}/"*.bel)
        fi

        if [ "${#tests[@]}" -gt 0 ]; then
            printf "%s\n" "${tests[@]}"
        fi
    done | sort -n
}

function usage {
    echo "Usage: $0 [test-options] -- [beluga-options]"
    echo
    echo "Synopsis: test harness for Beluga."
    echo
    echo "Options:"
    echo "  -h,--help        Display this usage information."
    echo "  -c,--color       Force colorized output even when piped."
    echo "  --printharpoon   Print harpoon output of a test when the test is failed."
    echo "                   This option implies --stop."
    echo "  --reset          Replace all .out files with new output (use with caution!)."
    echo "  --stop           Stop on the first failed test."
    echo
    echo "Notes:"
    echo "  - If any .cfg files are found in a subdirectory, only them will be tested."
    echo "  - If no .cfg file is found, all .bel files in the subdirectory"
    echo "    will be tested."
    echo "  - To inhibit testing .bel files, put an empty test.cfg in that directory."
}

function print_paths {
    echo "Parameters for this run (override as necessary using environment variables):"
    echo
    echo -e "\t BELUGA: ${BELUGA}"
    echo -e "\t HARPOON: ${HARPOON}"
    echo -e "\t REPLAY: ${REPLAY}"
    echo -e "\t TESTDIR: ${TESTDIR}"
    echo -e "\t INTERACTIVE_TESTDIR: ${INTERACTIVE_TESTDIR}"
    echo -e "\t EXAMPLEDIR: ${EXAMPLEDIR}"
    echo -e "\t TIMEOUT: ${TIMEOUT}" seconds
    echo
}

function set_colors {
    C_START="\x1b[34m"              # foreground blue
    C_ADMISSIBLE="\x1b[01;33m"      # foreground bold yellow
    C_OK="\x1b[01;32m"              # foreground bold green
    C_TIMEOUT="\x1b[01;35m"         # foreground bold magenta
    C_FAIL="\x1b[01;31m"            # foreground bold red
    C_LEXER_FAIL="\x1b[01;36m"      # foreground bold cyan
    C_ADDED="\x1b[32m"              # foreground green
    C_REMOVED="\x1b[31m"            # foreground red

    C_END="\x1b[00m"                # reset colors
}

main "$@"
