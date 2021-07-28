package bitte

import (
	"github.com/input-output-hk/plutus-ops/pkg/schemas/nomad:types"
	jobDef "github.com/input-output-hk/plutus-ops/pkg/jobs:jobs"
	"list"
)

let fqdn = "plutus.aws.iohkdev.io"
let opsRev = "95684007c17037c6ee139dceab7ee2417effb701"

Namespace: [Name=_]: {
	vars: {
		let hex = "[0-9a-f]"
		let seg = "[-a-zA-Z0-9]"
		let datacenter = "eu-central-1"
		let flakePath = "github:input-output-hk/\(seg)+\\?rev=\(hex){40}#\(seg)"

		datacenters: list.MinItems(1) | [...datacenter] | *[ "eu-central-1"]
		namespace:   Name
		#domain:     string
		#fqdn:       fqdn
		#opsRev:     =~"^\(hex){40}$" | *opsRev
		#flakes: [string]: types.#flake

		#flakes: {
			devBox: =~flakePath | *"github:input-output-hk/erc20-ops?rev=\(#opsRev)#devbox-entrypoint"
			// frontend:                =~flakePath | *"github:input-output-hk/erc20-ops?rev=\(#opsRev)#frontend-foo-entrypoint"
			webGhcServer:                =~flakePath | *"github:input-output-hk/plutus-ops?rev=\(#opsRev)#web-ghc-server-entrypoint"
			"plutus-playground-server":  =~flakePath | *"github:input-output-hk/plutus-ops?rev=\(#opsRev)#plutus-playground-server-entrypoint"
			"plutus-playground-client":  =~flakePath | *"github:input-output-hk/plutus-ops?rev=\(#opsRev)#plutus-playground-client-entrypoint"
			"marlowe-playground-server": =~flakePath | *"github:input-output-hk/plutus-ops?rev=\(#opsRev)#marlowe-playground-server-entrypoint"
			"marlowe-playground-client": =~flakePath | *"github:input-output-hk/plutus-ops?rev=\(#opsRev)#marlowe-playground-client-entrypoint"
		}

		#rateLimit: {
			average: uint | *100
			burst:   uint | *250
			period:  types.#duration | *"1m"
		}
	}
	jobs: [string]: types.#stanza.job
}

#namespaces: Namespace

#namespaces: {
	"plutus-playground": {
		vars: {
			// Namespace specific var overrides and additions
			// #opsRev: ""
		}
		jobs: {
			"web-ghc-server": jobDef.#WebGhcServerJob & {
				#domain: "web-ghc.\(fqdn)"
			}
			"plutus-playground": jobDef.#PlutusPlaygroundJob & {
				#domain:      "plutus-playground.\(fqdn)"
				#variant:     "plutus"
			}
			"marlowe-playground": jobDef.#PlutusPlaygroundJob & {
				#domain:      "marlowe-playground.\(fqdn)"
				#variant:     "marlowe"
			}
		}
	}
}

for nsName, nsValue in #namespaces {
	rendered: "\(nsName)": {
		for jName, jValue in nsValue.jobs {
			"\(jName)": Job: types.#toJson & {
				#jobName: jName
				#job:     jValue & nsValue.vars
			}
		}
	}
}

for nsName, nsValue in #namespaces {
	// output is alphabetical, so better errors show at the end.
	zchecks: "\(nsName)": {
		for jName, jValue in nsValue.jobs {
			"\(jName)": jValue & nsValue.vars
		}
	}
}
