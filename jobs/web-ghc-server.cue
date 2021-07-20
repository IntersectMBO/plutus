package jobs

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	"github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#WebGhcServerJob: types.#stanza.job & {
	#flakes: [string]: types.#flake

	namespace: string

	type: "service"

	group: devbox: {
		network: {
			mode: "host"
			port: web-ghc-server: { static: 8009 }
		}
		// Keep count at 1 for now with higher CPU / RAM resources
		count: 1

		task: "devbox": tasks.#WebGhcServerTask & {
			#flake:     #flakes.devBox
			#namespace: namespace
		}
	}
}
