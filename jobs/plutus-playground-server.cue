package jobs

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	"github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#PlutusPlaygroundServerJob: types.#stanza.job & {
	#domain:         string
	#fqdn:           string
	#flakes: [string]: types.#flake
	#hosts:          string
	#rateLimit: {
		average: uint
		burst:   uint
		period:  types.#duration
	}
	#hosts: "`\(#domain)`,`server.\(#fqdn)`"

	namespace: string

	type: "service"

	group: server: {
		network: {
			mode: "host"
			port: "plutus-playground-server": { static: 4003 }
		}
		// Keep count at 1 for now with higher CPU / RAM resources
		count: 1

		service: "\(namespace)-plutus-playground-server": {
			address_mode: "host"
			port:         "plutus-playground-server"

			tags: [
				namespace,
				"ingress",
				"traefik.enable=true",
				"traefik.http.routers.\(namespace)-plutus-playground-server.rule=Host(\(#hosts))",
				"traefik.http.routers.\(namespace)-plutus-playground-server.entrypoints=https",
				"traefik.http.routers.\(namespace)-plutus-playground-server.tls=true",
				"traefik.http.routers.\(namespace)-plutus-playground-server.middlewares=\(namespace)-web-ghc-server-ratelimit@consulcatalog",
				"traefik.http.middlewares.\(namespace)-plutus-playground-server-ratelimit.ratelimit.average=\(#rateLimit.average)",
				"traefik.http.middlewares.\(namespace)-plutus-playground-server-ratelimit.ratelimit.burst=\(#rateLimit.burst)",
				"traefik.http.middlewares.\(namespace)-plutus-playground-server-ratelimit.ratelimit.period=\(#rateLimit.period)",
			]

			//check: "health": {
			//	type:     "http"
			//	port:     "web-ghc-server"
			//	interval: "10s"
			//	path:     "/health"
			//	timeout:  "2s"
			//}
		}

		task: "plutus-playground-server": tasks.#SimpleTask & {
			#flake:     #flakes."plutus-playground-server"
			#namespace: namespace
		}
	}
}
