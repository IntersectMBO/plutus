package jobs

import (
        "github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
        "github.com/input-output-hk/plutus-ops/pkg/jobs/tasks:tasks"
)

#MarloweRunJob: types.#stanza.job & {
        #domain:         string
        #fqdn:           string
        #flakes: [string]: types.#flake
        #hosts:          string
        #rateLimit: {
                average: uint
                burst:   uint
                period:  types.#duration
        }
        #hosts: "`\(#domain)`,`marlowe-run.\(#fqdn)`"

        namespace: string

        type: "service"

        group: server: {
                network: {
                        mode: "host"
                        port: "marlowe-run": { static: 9080 }
                        port: "pab-node": { static: 8082 }
                        port: "pab-chain-index": { static: 8083 }
                        port: "pab-signing-process": { static: 8084 }
                        port: "pab-metadata": { static: 8085 }
                        port: "pab-wallet": { static: 8086 }
                }
                count: 1

                service: "\(namespace)-marlowe-run": {
                        address_mode: "host"
                        port:         "marlowe-run"

                        tags: [
                                namespace,
                                "ingress",
                                "traefik.enable=true",
                                "traefik.http.routers.\(namespace)-marlowe-run.rule=Host(\(#hosts))",
                                "traefik.http.routers.\(namespace)-marlowe-run.entrypoints=https",
                                "traefik.http.routers.\(namespace)-marlowe-run.tls=true",
                                "traefik.http.routers.\(namespace)-marlowe-run.middlewares=\(namespace)-marlowe-run-ratelimit@consulcatalog",
                                "traefik.http.middlewares.\(namespace)-marlowe-run-ratelimit.ratelimit.average=\(#rateLimit.average)",
                                "traefik.http.middlewares.\(namespace)-marlowe-run-ratelimit.ratelimit.burst=\(#rateLimit.burst)",
                                "traefik.http.middlewares.\(namespace)-marlowe-run-ratelimit.ratelimit.period=\(#rateLimit.period)",
                        ]

                        check: "health": {
                                type:     "http"
                                port:     "marlowe-run"
                                interval: "10s"
                                path:     "/api/healthcheck"
                                timeout:  "2s"
                        }
                }

                volume: "pab": types.#stanza.volume & {
                  type:       "host"
                  source:     "pab"
                  read_only:  false
                }

                task: "marlowe-run": tasks.#SimpleTask & {
                        #flake:     #flakes.marloweRun
                        #namespace: namespace
                        #fqdn: #fqdn
                        #memory: 1024
                        #domain: #domain
                        #volumeMount: "pab": types.#stanza.volume_mount & {
                          volume: "pab"
                          destination: "/var/lib/pab"
                        }
                }
        }
}
