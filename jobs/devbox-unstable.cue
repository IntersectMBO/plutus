package jobs

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	"github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#DevBoxUnstableJob: types.#stanza.job & {
	#flakes: [string]: types.#flake

	namespace: string

	type: "service"

	group: devbox: {
		// Keep count at 1 for now with higher CPU / RAM resources
		count: 1

		task: "devbox": tasks.#DevBoxUnstableTask & {
			#flake:     #flakes.devBox
			#namespace: namespace
		}
	}
}
