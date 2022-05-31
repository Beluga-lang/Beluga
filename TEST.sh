#!/usr/bin/env bash

# Emit an error if undefined variable is used.
set -u

shopt -s nullglob

# Option flags.
declare FORCE_COLOR_OUTPUT=""
declare NO_EXAMPLES=""
declare ONLY_EXAMPLES=""
declare ONLY_INTERACTIVES=""
declare ONLY_HARPOON=""
declare PRINT_HARPOON_OUTPUT_ON_FAILURE=""
declare RESET_OUT_FILES=""
declare STOP_ON_FAILURE=""

declare -a BELUGA_FLAGS=()

declare -r ROOTDIR=${ROOTDIR:-$(pwd)}
declare -r TEMPDIR=${TEMPDIR:-$(mktemp -d)}
declare SKIP_RSYNC=0

declare -r TESTROOTDIR=${TESTROOTDIR:-"./t"}
declare -r TESTDIR=${TESTDIR:-"${TESTROOTDIR}/code"}
declare -r EXAMPLEDIR=${EXAMPLEDIR:-"./examples"}
declare -r INTERACTIVE_TESTDIR=${INTERACTIVE_TESTDIR:-"${TESTROOTDIR}/interactive"}
declare -r HARPOON_TESTDIR=${HARPOON_TESTDIR:-"${TESTROOTDIR}/harpoon"}

declare -i TIMEOUT=${TIMEOUT:-10}

function rsync_test_artifacts {
    rsync -ak "${ROOTDIR}/.admissible-fail" "${TEMPDIR}/.admissible-fail"
    rsync -ak "${ROOTDIR}/run_harpoon_test.sh" "${TEMPDIR}/run_harpoon_test.sh"
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
    if [ ${SKIP_RSYNC} -eq 1 ] ; then
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
            --noexamples)
                NO_EXAMPLES="true"
                ;;
            --examples)
                ONLY_EXAMPLES="true"
                ;;
            --reset)
                SKIP_RSYNC=1
                RESET_OUT_FILES="true"
                ;;
            --interactive)
                ONLY_INTERACTIVES="true"
                ;;
            --harpoon)
                ONLY_HARPOON="true"
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
    local exit_code=0 is_failed=0
    # Limit runtime of each test case, in seconds.
    ulimit -t "${TIMEOUT}"

    if [[ -z "${NO_EXAMPLES}" && -z "${ONLY_INTERACTIVES}" && -z "${ONLY_HARPOON}" ]]; then
        echo "===== EXAMPLES ====="

        for f in $(find_compiler_tests_in "${EXAMPLEDIR}"); do
            start_test_case "${f}"

            if ! lex_check_test_case "${f}"; then
                continue
            fi

            check_compiler_test_case "${f}"
        done
    fi

    if [[ -z "${ONLY_EXAMPLES}" && -z "${ONLY_INTERACTIVES}" && -z "${ONLY_HARPOON}" ]]; then
        echo "===== COMPILER TESTS ====="

        for f in $(find_compiler_tests_in "${TESTDIR}") ; do
            start_test_case "${f}"

            if ! lex_check_test_case "${f}"; then
                continue
            fi

            check_compiler_test_case "${f}"
        done
    fi

    if [[ -z "${ONLY_HARPOON}" ]]; then
        echo "===== INTERACTIVE MODE TESTS ====="

        for f in $(find "${INTERACTIVE_TESTDIR}" -type f | sort -n) ; do
            start_test_case "${f}"

            local exe=$(which beluga)
            local output="$(replay "${exe}" "${f}")"
            exit_code=$?

            if [ "${exit_code}" -eq 152 ] ; then
                echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
                (( TEST_RESULT_TIMEOUT+=1 ))
            elif [ "${exit_code}" -ne 0 ] ; then
                echo -e "${C_FAIL}FAIL${C_END}"
                (( TEST_RESULT_FAIL+=1 ))
                echo "${output}"
            else
                echo -e "${C_OK}OK${C_END}"
                (( TEST_RESULT_SUCCESS+=1 ))
            fi
        done
    fi

    echo "===== HARPOON MODE TESTS ====="

    for f in $(find "${HARPOON_TESTDIR}" -type f -name "*.input" | sort -n) ; do
        start_test_case "${f}"

        check_harpoon "${f}"
    done

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

function lex_check_test_case {
    local -r file_path=$1

    local exit_code

    lex_check "${file_path}" > /dev/null 2>&1
    exit_code=$?

    if [ "${exit_code}" -eq 2 ] ; then
        echo -e "${C_FAIL}FATAL LEXER FAILURE${C_END}"
        (( TEST_RESULT_LEXER_FAIL+=1 ))
        stop_on_failure
        return 1
    fi

    if [ "${exit_code}" -ne 0 ] ; then
        echo -e "${C_FAIL}LEXER FAILURE${C_END}"
        (( TEST_RESULT_LEXER_FAIL+=1 ))
        stop_on_failure
        return 1
    fi

    return 0
}

function check_compiler_test_case {
    local -r file_path=$1

    local output exit_code diff_output diff_code

    # ${...[@]+${...[@]}} is a workaround for bash < 4.4
    # In bash < 4.4, array without an item is considered as an undefined variable.
    output=$(beluga +test "${BELUGA_FLAGS[@]+${BELUGA_FLAGS[@]}}" "${file_path}" 2>&1)
    exit_code=$?
    diff_output=$(printf "%s" "${output}" | diff -b -u "${file_path}.out" - 2>/dev/null)
    # diff responds 0 if same, 1 if different, 2 if couldn't compare.
    diff_code=$?

    if [ "${exit_code}" -eq 152 ];then
        echo -e "${C_TIMEOUT}TIMEOUT${C_END}"
        (( TEST_RESULT_TIMEOUT+=1 ))
        stop_on_failure
    elif [[ "${diff_code}" -eq 0 || ("${exit_code}" -eq 0 && "${diff_code}" -eq 2) ]]; then
        echo -e "${C_OK}OK${C_END}"
        (( TEST_RESULT_SUCCESS+=1 ))
    else
        if grep -q "${file_path}" .admissible-fail ; then
            echo -e "${C_ADMISSIBLE}ADMISSIBLE${C_END}"
            (( TEST_RESULT_ADMISSIBLE+=1 ))
        else
            echo -e "${C_FAIL}FAIL${C_END}"
            (( TEST_RESULT_FAIL+=1 ))

            if [ -z "${diff_output}" ]; then
                echo "${output}"
            else
                echo "${diff_output}" | colorize_diff
            fi

            stop_on_failure
        fi
    fi

    if [[ -n "${RESET_OUT_FILES}" && -f "${file_path}.out" ]]; then
        echo "${output}" > "${file_path}.out"
    fi
}

function check_harpoon {
    local -r file_path=$1

    local output exit_code

    output=$(./run_harpoon_test.sh "${file_path}" --no-save-back --stop 2>&1)
    exit_code=$?

    if [ ${exit_code} -ne 0 ] ; then
        echo -e "${C_FAIL}FAIL${C_END}"
        (( TEST_RESULT_HARPOON_FAIL+=1 ))
        print_harpoon_output_on_failure "${output}"
        stop_on_failure
    else
        echo -e "${C_OK}OK${C_END}"
        (( TEST_RESULT_SUCCESS+=1 ))
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

    for dir in $(find "$1" -mindepth 1 -type d) ; do
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
    echo "  --noexamples     Do not also test ${EXAMPLEDIR}."
    echo "  --examples       Only test ${EXAMPLEDIR}."
    echo "  --interactive    Only test the interactive mode."
    echo "  --harpoon        Only test the harpoon mode."
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
    C_END="\x1b[00m"                     # reset colors
}

function colorize_diff {
    sed "s/^+/${C_ADDED}+/
         s/^-/${C_REMOVED}-/
         s/\$/${C_END}/"
}

main "$@"
