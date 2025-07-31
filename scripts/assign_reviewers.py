"""
Download and parse a .json file containing reviewer assignments for pull requests,
and make the github API calls to add these users as assignees.

This script assumes |curl| is installed and on PATH.
"""
import json
import os
import sys
import subprocess

ASSIGN_REVIEWERS_TOKEN = os.getenv('ASSIGN_REVIEWERS_TOKEN')
if ASSIGN_REVIEWERS_TOKEN is None:
    print('Please ensure that the ASSIGN_REVIEWERS_TOKEN environment variable is set.')
    sys.exit(1)

# Make the github API call to assign mathlib PR |number| to user |handle|.
# Any existing assignee is kept; specifying a non-existent user does nothing.
# Github's assignment syntax is documented at
# https://docs.github.com/en/rest/issues/assignees?apiVersion=2022-11-28#add-assignees-to-an-issue.
def call(number: int, handle: str) -> bool:
    print(f"assigning PR {number} to {handle}")
    url = f"https://api.github.com/repos/leanprover-community/mathlib4/issues/{number}/assignees"
    arguments_DO_NOT_PRINT = [
        "--fail-with-body", "--location", "--request", "POST",
        '--header', 'Accept: application/vnd.github+json',
        '--header', f"authorization: Bearer {ASSIGN_REVIEWERS_TOKEN}",
        '--header', "X-GitHub-Api-Version: 2022-11-28",
        url, '--data', f'{{"assignees":["{handle}"]}}'
    ]
    out = subprocess.run(["curl"] + arguments_DO_NOT_PRINT, capture_output=True, encoding="utf-8")
    print("output from calling CURL:\n" + out.stdout)
    if out.stderr:
        print("standard error output is:\n" + out.stderr)
    if out.returncode != 0:
        print(f"error: curl failed to assign reviewer {handle} to PR {number}")
        return False
    return True

# Ping the queueboard webhook to trigger a re-download of PR |number|'s data.
# Caution: at the moment, care is necessary to call this at the right moment
# (otherwise, this will invalidate the queueboard CI jobs). Only call manually when the time is right.
def ping_queueboard_update(number: int) -> bool:
    print(f"pinging a queueboard data re-download of PR {number}")
    url = "https://api.github.com/repos/leanprover-community/queueboard/dispatches"
    arguments_DO_NOT_PRINT = [
        # XXX: --location is not passed
        "--request", "POST",
        '--header', 'Content-Type: application/json',
        '--header', 'Accept: application/vnd.github+json',
        '--header', f"Authorization: token {ASSIGN_REVIEWERS_TOKEN}",
        '--header', "X-GitHub-Api-Version: 2022-11-28",
        '--data', f'{{"event_type": "mathlib_ping", "client_payload": {{"pr_number": "{number}" }} }}',
        url
    ]
    out = subprocess.run(["curl"] + arguments_DO_NOT_PRINT, capture_output=True, encoding="utf-8")
    print("output from calling CURL:\n" + out.stdout)
    if out.stderr:
        print("standard error output is:\n" + out.stderr)
    if out.returncode != 0:
        print(f"error: curl failed to ping a data re-download for PR {number}")
        return False
    return True

if __name__ == '__main__':
    # Download the assignments file using curl
    url = "https://leanprover-community.github.io/queueboard/automatic_assignments.json"
    args = ["curl", "--output", "assignments.json", url]
    print("trace: about to download the assignments file using curl...")
    out = subprocess.run(args, capture_output=True, encoding="utf-8")
    if out.stdout:
        print("standard output is: \n" + out.stdout)
    if out.stderr:
        print("standard error is: \n" + out.stderr)
    if out.returncode != 0:
        print(f"error: curl failed to download the assignment file at {url}"
            "Please make sure curl is installed and on your PATH.")
        sys.exit(1)

    with open('assignments.json', 'r') as fi:
        data = json.load(fi)
    all_api_calls_succeeded = True
    for (number, user_handle) in data.items():
        pass#all_api_calls_succeeded = all_api_calls_succeeded and call(number, user_handle)

    to_ping = [
        # insert PRs here
    ]
    for number in to_ping:
        all_api_calls_succeeded = all_api_calls_succeeded and ping_queueboard_update(number)
        # TODO: sleep for 10 or 12 seconds between subsequent calls!
        # (or pass multiple PRs to the script!)
    # XXX: can there be a quick job which just updates aggregate data and the webpage?
    # (or would that also take ages?)

    if not all_api_calls_succeeded:
        sys.exit(1)
