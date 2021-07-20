package bitte

import (
	"encoding/json"
	"tool/cli"
)

#jobName:   string @tag(job)
#namespace: string @tag(namespace)

command: render: {
	display: cli.Print & {
		text: json.Indent(json.Marshal(
			rendered[#namespace][#jobName],
			), "", "  ")
	}
}
