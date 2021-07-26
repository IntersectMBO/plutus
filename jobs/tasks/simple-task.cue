package tasks

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
)

#SimpleTask: types.#stanza.task & {
	#flake: types.#flake

	#namespace: string
        #memory: uint
        #fqdn: string
	#variant: string
	#domain: string

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
	env: {
		// TODO, only needs to be set for the server component
		// TODO, should be based on fqdn
		WEBGHC_URL: "web-ghc.plutus.aws.iohkdev.io)"
		PATH: "/bin"
		FRONTEND_URL: "https://\(#domain)"
	}
	// TODO, only present for server component
	template: "secrets/env.txt": {
		data: """
			{{with secret "kv/nomad-cluster/\(#namespace)/\(#variant)/github"}}
			GITHUB_CLIENT_ID="{{.Data.data.GITHUB_CLIENT_ID}}"
			GITHUB_CLIENT_SECRET="{{.Data.data.GITHUB_CLIENT_SECRET}}"
			{{end}}
			"""
		change_mode: "restart"
		env: true
	}
}
