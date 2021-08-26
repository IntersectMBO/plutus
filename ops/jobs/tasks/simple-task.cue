package tasks

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
)

#SimpleTask: types.#stanza.task & {
	#flake: types.#flake

	#namespace: string
	#memory: uint
	#extraEnv: [string]: string
	#envTemplate: *null | string
	#volumeMount: [string]: types.#stanza.volume_mount

	driver: "exec"

	kill_timeout: "30s"

	vault: {
		policies:    [ "nomad-cluster" ]
		change_mode: "noop"
	}

	resources: {
		cpu:    4000
		memory: #memory
	}

	config: {
		flake:   #flake
		command: "/bin/entrypoint"
	}
	let baseEnv = {
		PATH: "/bin"
	}
	env: baseEnv & #extraEnv
	if #envTemplate != null {
		template:
		"secrets/env.txt": {
			data: #envTemplate
			change_mode: "restart"
			env: true
		}
	}
	volume_mount: #volumeMount
}
