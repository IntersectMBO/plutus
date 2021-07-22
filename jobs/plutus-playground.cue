package jobs

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	"github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#PlutusPlaygroundJob: types.#stanza.job & {
	#domain:         string
	#fqdn:           string
	#flakes: [string]: types.#flake
	#hosts:          string
	#variant:        string
	#serverFlake: string
	#clientFlake: string
	#rateLimit: {
		average: uint
		burst:   uint
		period:  types.#duration
	}
	#hosts: "`\(#domain)`,`client.\(#fqdn)`"

	namespace: string

	type: "service"

	group: "\(#variant)-playground": {
		network: {
			mode: "host"
			port: {
				"\(#variant)-playground-client": { static: 8081 }
				"\(#variant)-playground-server": { static: 4003 }
			}
		}
		// Keep count at 1 for now with higher CPU / RAM resources
		count: 1

		service: "\(namespace)-\(#variant)-playground-client": {
			address_mode: "host"
			port:         "\(#variant)-playground-client"

			tags: [
				namespace,
				"ingress",
				"traefik.enable=true",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-client.rule=Host(\(#hosts))",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-client.entrypoints=https",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-client.tls=true",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-client.middlewares=\(namespace)-\(#variant)-playground-client-ratelimit@consulcatalog",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-client-ratelimit.ratelimit.average=\(#rateLimit.average)",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-client-ratelimit.ratelimit.burst=\(#rateLimit.burst)",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-client-ratelimit.ratelimit.period=\(#rateLimit.period)",
			]
		}

		service: "\(namespace)-\(#variant)-playground-server": {
			address_mode: "host"
			port:         "\(#variant)-playground-server"

			tags: [
				namespace,
				"ingress",
				"traefik.enable=true",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-server.rule=Host(\(#hosts)) && PathPrefix(`/api/`)",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-server.entrypoints=https",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-server.tls=true",
				"traefik.http.routers.\(namespace)-\(#variant)-playground-server.middlewares=\(namespace)-web-ghc-server-ratelimit@consulcatalog",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-server-ratelimit.ratelimit.average=\(#rateLimit.average)",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-server-ratelimit.ratelimit.burst=\(#rateLimit.burst)",
				"traefik.http.middlewares.\(namespace)-\(#variant)-playground-server-ratelimit.ratelimit.period=\(#rateLimit.period)",
			]
		}

		task: "client": tasks.#SimpleTask & {
			#flake:     #clientFlake
			#namespace: namespace
			#memory: 32
		}

		task: "server": tasks.#SimpleTask & {
			#flake:     #serverFlake
			#namespace: namespace
			#memory: 32
		}
	}
}
