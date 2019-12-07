#! /usr/bin/env bash

set -euvx

if [ "$#" -lt 2 ]
then
    echo "usage: ${BASH_SOURCE[0]} <travis_api_token> <job_id>"
    exit 1
fi

# Checks whether $2 (i.e. JOB_ID) is integer or not.
if ! [ "$2" -eq "$2" ] 2> /dev/null
then
    echo "usage: ${BASH_SOURCE[0]} <travis_api_token> <job_id>"
    echo ""
    echo "Error: <job_id> should be an integer, but receives $2"
    exit 1
fi

declare -r TRAVIS_API_TOKEN="$1"
declare -i JOB_ID="$2"

curl -s -X POST \
    -H "Content-Type: application/json" \
    -H "Accept: application/json" \
    -H "Travis-API-Version: 3" \
    -H "Authorization: token ${TRAVIS_API_TOKEN}" \
    -d '{ "quiet": true }' \
    "https://api.travis-ci.org/job/${JOB_ID}/debug"
