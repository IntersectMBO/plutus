package jobs

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	"github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#WebGhcServerJob: types.#stanza.job & {
	#domain:         string
	#fqdn:           string
	#flakes: [string]: types.#flake
	#hosts:          string
	#rateLimit: {
		average: uint
		burst:   uint
		period:  types.#duration
	}
        #hosts: "`\(#domain)`,`frontend.\(#fqdn)`"

	namespace: string

	type: "service"

	group: server: {
		network: {
			mode: "host"
			port: "web-ghc-server": { static: 8009 }
		}
		// Keep count at 1 for now with higher CPU / RAM resources
		count: 1

		service: "\(namespace)-web-ghc-server": {
			address_mode: "host"
			port:         "web-ghc-server"

			tags: [
				namespace,
				"ingress",
				"traefik.enable=true",
				"traefik.http.routers.\(namespace)-web-ghc-server.rule=Host(\(#hosts))",
				"traefik.http.routers.\(namespace)-web-ghc-server.entrypoints=https",
				"traefik.http.routers.\(namespace)-web-ghc-server.tls=true",
				"traefik.http.routers.\(namespace)-web-ghc-server.middlewares=\(namespace)-web-ghc-server-ratelimit@consulcatalog",
				"traefik.http.middlewares.\(namespace)-web-ghc-server-ratelimit.ratelimit.average=\(#rateLimit.average)",
				"traefik.http.middlewares.\(namespace)-web-ghc-server-ratelimit.ratelimit.burst=\(#rateLimit.burst)",
				"traefik.http.middlewares.\(namespace)-web-ghc-server-ratelimit.ratelimit.period=\(#rateLimit.period)",
			]

			check: "health": {
				type:     "http"
				port:     "web-ghc-server"
				interval: "10s"
				path:     "/health"
				timeout:  "2s"
			}
		}

		task: "web-ghc-server": tasks.#WebGhcServerTask & {
			#flake:     #flakes.webGhcServer
			#namespace: namespace
		}
	}
}
