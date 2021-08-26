package tasks

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
)

#DevBoxUnstableTask: types.#stanza.task & {
	#flake: types.#flake

	#namespace: string

	driver: "exec"

	kill_timeout: "30s"

	//vault: {
	//	policies:    [ "nomad-cluster" ]
	//	change_mode: "noop"
	//}

	resources: {
		cpu:    4000
		memory: 5120
	}

	config: {
		flake:   #flake
		command: "/bin/entrypoint"
	}

	template: "secrets/env.txt": {
		data: """
			{{with secret "kv/nomad-cluster/\(#namespace)/database"}}
				PATH="/bin"
				# Required for patroni which errors if scheme is included
				CONSUL_HTTP_ADDR="127.0.0.1:8500"
				HA="\(#namespace)-database"
				DB_USER="{{.Data.data.dbUser}}"
				TERM="xterm-256color"
			{{end}}
		"""
		env: true
	}
}
