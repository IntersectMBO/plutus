# How to test workflow tests using the act tool 
# 0. Make sure your docker daemon is running
# 1. Inside the shell, run: act -W .github/workflows/slack-message-broker.yml --container-architecture linux/amd64 -e test-event.json
# Where test-event.json looks a little like this:
{
  "worflow_run": {
    "name": ""
  }
}
