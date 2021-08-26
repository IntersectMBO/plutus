// INFORMATION:
//
// This file acts as a CUE type schema for nomad JSON job submission in bitte end use repos.
// This ensures that JSON jobs created by CUE conform to Nomads JSON job spec found at:
//
//   https://www.nomadproject.io/api-docs/json-jobs
//
// Not all valid Nomad JSON job options may be included here yet; this file can be extended as needed.
// If expected Nomad job properties are still not appearing in deployed jobs, check that bitte-cli
// is allowing the expected JSON through the [de]serialization parsing.
//
// In bitte end use repos, this file normally lives at:
//
//   schemas/nomad/types.cue
//
package types

import (
	"time"
	"list"
)

// The #json block defines the final JSON structure and values types.
#json: {
	Job: {
		Namespace:   string
		ID:          Name
		Name:        string
		Type:        "service" | "system" | "batch"
		Priority:    uint
		Datacenters: list.MinItems(1)
		TaskGroups:  [...TaskGroup]
		Affinities:  [...Affinity]
		Constraints: [...Constraint]
		Spreads:     [...Spread]
		ConsulToken: *null | string
		VaultToken:  *null | string
		Vault:       *null | #json.Vault
		Update:      *null | #json.Update
	}

	Affinity: {
		LTarget: string
		RTarget: string
		Operand: "regexp" | "set_contains_all" | "set_contains" | "set_contains_any" | "=" | "==" | "is" | "!=" | "not" | ">" | ">=" | "<" | "<=" | "version"
		Weight:  uint & !=0 & >=-100 & <=100
	}

	Constraint: {
		LTarget: string | *null
		RTarget: string
		Operand: "regexp" | "set_contains" | "distinct_hosts" | "distinct_property" | "=" | "==" | "is" | "!=" | "not" | ">" | ">=" | "<" | "<="
	}

	Spread: {
		Attribute:    string
		Weight:       uint & >=-100 & <=100 | *null
		SpreadTarget: [...SpreadTargetElem]
	}

	SpreadTargetElem: {
		Value:   string
		Percent: uint & >=0 & <=100 | *null
	}

	RestartPolicy: {
		Attempts: uint
		Interval: uint
		Delay:    uint
		Mode:     "delay" | "fail"
	}

	Volume: {
		Name:     string
		Type:     *null | "host" | "csi"
		Source:   string
		ReadOnly: bool | *false
		MountOptions: *null | {
			FsType:     *null | string
			mountFlags: *null | string
		}
	}

	ReschedulePolicy: {
		Attempts:      *null | uint
		DelayFunction: *null | "constant" | "exponential" | "fibonacci"
		Delay:         *null | uint & >=time.ParseDuration("5s")
		Interval:      *null | uint
		MaxDelay:      *null | uint
		Unlimited:     *null | bool
	}

	Restart: {
		Attempts: uint
		Delay:    uint
		Interval: uint
		Mode:     "fail" | "delay"
	}

	Migrate: {
		HealthCheck:     *"checks" | "task_states"
		HealthyDeadline: uint | *500000000000
		MaxParallel:     uint | *1
		MinHealthyTime:  uint | *10000000000
	}

	Update: {
		AutoPromote:      bool | *false
		AutoRevert:       bool | *false
		Canary:           uint | *0
		HealthCheck:      *"checks" | "task_states" | "manual"
		HealthyDeadline:  uint | *null
		MaxParallel:      uint | *1
		MinHealthyTime:   uint | *null
		ProgressDeadline: uint | *null
		Stagger:          uint | *null
	}

	TaskGroup: {
		Affinities:                [...Affinity]
		Constraints:               [...Constraint]
		Spreads:                   [...Spread]
		Count:                     int & >0 | *1
		Meta:                      [string]: string
		Name:                      string
		RestartPolicy:             *null | #json.RestartPolicy
		Restart:                   #json.Restart
		Services:                  [...Service]
		ShutdownDelay:             uint | *0
		Tasks:                     [...Task]
		Volumes:                   [string]: #json.Volume
		ReschedulePolicy:          #json.ReschedulePolicy
		EphemeralDisk:             *null | {
			Migrate: bool
			SizeMB:  uint
			Sticky:  bool
		}
		Migrate:                   #json.Migrate
		Update:                    *null | #json.Update
		Networks:                  [...#json.Network]
		StopAfterClientDisconnect: *null | uint
		Scaling:                   null
		Vault:                     *null | #json.Vault
	}

	Port: {
		Label:       string
		Value:       uint | *null // used for static ports
		To:          uint | *null
		HostNetwork: string | *""
	}

	Network: {
		Mode:          *"host" | "bridge"
		Device:        string | *""
		CIDR:          string | *""
		IP:            string | *""
		DNS:           null
		ReservedPorts: *null | [...#json.Port]
		DynamicPorts:  *null | [...#json.Port]
		MBits:         null
	}

	ServiceCheck: {
		AddressMode:            "alloc" | "driver" | "host"
		Args:                   [...string] | *null
		CheckRestart:           #json.CheckRestart
		Command:                string | *""
		Expose:                 false
		FailuresBeforeCritical: uint | *0
		Id:                     string | *""
		InitialStatus:          string | *""
		Interval:               uint | *10000000000
		Method:                 string | *""
		Name:                   string | *""
		Path:                   string | *""
		PortLabel:              string
		Protocol:               string | *""
		SuccessBeforePassing:   uint | *0
		TaskName:               string | *""
		Timeout:                uint
		TLSSkipVerify:          bool | *false
		Type:                   "http" | "tcp" | "script" | "grpc"
		Body:                   string | *null
		Header: [string]: [...string]
	}

	CheckRestart: *null | {
		Limit:          uint | *0
		Grace:          uint | *10000000000
		IgnoreWarnings: bool | *false
	}

	Lifecycle: {
		Hook:    "prestart" | "poststart" | "poststop"
		Sidecar: bool | *null
	}

	LogConfig: *null | {
		MaxFiles:      uint & >0
		MaxFileSizeMB: uint & >0
	}

	Service: {
		Id:                string | *""
		Name:              string
		Tags:              [...string]
		CanaryTags:        [...string] | *[]
		EnableTagOverride: bool | *false
		PortLabel:         string
		AddressMode:       "alloc" | "auto" | "driver" | "host"
		Checks:            [...ServiceCheck]
		CheckRestart:      #json.CheckRestart
		Connect:           null
		Meta:              [string]: string
		TaskName:          string | *""
	}

	Task: {
		Name:            string
		Driver:          "exec" | "docker" | "nspawn"
		Config:          #stanza.taskConfig & {#driver: Driver}
		Constraints:     [...Constraint]
		Affinities:      [...Affinity]
		Env:             [string]: string
		Services:        [...Service]
		Resources: {
			CPU:      uint & >=100 | *100
			MemoryMB: uint & >=32 | *300
			DiskMB:   *null | uint
		}
		Meta:            {}
		RestartPolicy:   *null | #json.RestartPolicy
		ShutdownDelay:   uint | *0
		User:            string | *""
		Lifecycle:       *null | #json.Lifecycle
		KillTimeout:     *null | uint
		LogConfig:       #json.LogConfig
		Artifacts:       [...#json.Artifact]
		Templates:       [...#json.Template]
		DispatchPayload: null
		VolumeMounts:    [...#json.VolumeMount]
		Leader:          bool | *false
		KillSignal:      string
		ScalingPolicies: null
		Vault:           *null | #json.Vault
	}

	VolumeMount: {
		Destination:     string
		PropagationMode: string
		ReadOnly:        bool
		Volume:          string
	}

	Artifact: {
		GetterSource: string
		GetterOptions: [string]: string
		GetterHeaders: [string]: string
		GetterMode:   *"any" | "file" | "dir"
		RelativeDest: string
	}

	Template: {
		SourcePath:   string | *""
		DestPath:     string
		EmbeddedTmpl: string
		ChangeMode:   *"restart" | "noop" | "signal"
		ChangeSignal: string | *""
		Splay:        uint | *5000000000
		Perms:        *"0644" | =~"^[0-7]{4}$"
		LeftDelim:    string
		RightDelim:   string
		Envvars:      bool
	}

	Vault: {
		ChangeMode:   "noop" | *"restart" | "signal"
		ChangeSignal: string | *""
		Env:          bool | *true
		Namespace:    string | *""
		Policies:     list.MinItems(1)
	}
}

#dockerUrlPath:  =~"^[0-9a-zA-Z-.]+/[0-9a-zA-Z-]+:[0-9a-zA-Z-]+$"
#duration:       =~"^[1-9]\\d*[hms]$"
#gitRevision:    =~"^[a-f0-9]{40}$"
#flake:          =~"^(github|git\\+ssh|git):[0-9a-zA-Z_-]+/[0-9a-zA-Z_-]+"


// The #toJson block is evaluated from deploy.cue during rendering of the namespace jobs.
// #job and #jobName are passed to #toJson during this evaluation.
// #toJson evaluation is constrained by the #json.Job block defined at the start of this file.
#toJson: #json.Job & {
	#job:        #stanza.job
	#jobName:    string
	Name:        #jobName
	Datacenters: #job.datacenters
	Namespace:   #job.namespace
	Type:        #job.type
	Priority:    #job.priority

	if #job.update != null {
		let u = #job.update
		Update: {
			AutoPromote:      u.auto_promote
			AutoRevert:       u.auto_revert
			Canary:           u.canary
			HealthCheck:      u.health_check
			HealthyDeadline:  time.ParseDuration(u.healthy_deadline)
			MaxParallel:      u.max_parallel
			MinHealthyTime:   time.ParseDuration(u.min_healthy_time)
			ProgressDeadline: time.ParseDuration(u.progress_deadline)
			Stagger:          time.ParseDuration(u.stagger)
		}
	}

	if #job.vault != null {
		Vault: {
			ChangeMode:   #job.vault.change_mode
			ChangeSignal: #job.vault.change_signal
			Env:          #job.vault.env
			Namespace:    #job.vault.namespace
			Policies:     #job.vault.policies
		}
	}

	Affinities: [ for a in #job.affinities {
		LTarget: a.attribute
		RTarget: a.value
		Operand: a.operator
		Weight:  a.weight
	}]

	Constraints: [ for c in #job.constraints {
		LTarget: c.attribute
		RTarget: c.value
		Operand: c.operator
	}]

	Spreads: [ for s in #job.spreads {
		Attribute:    s.attribute
		Weight:       s.weight
		SpreadTarget: [ for t in s.target {
			Value:   t.value
			Percent: t.percent
		}]
	}]

	TaskGroups: [ for tgName, tg in #job.group {
		Name: tgName

		Count: tg.count

		Affinities: [ for a in tg.affinities {
			LTarget: a.attribute
			RTarget: a.value
			Operand: a.operator
			Weight:  a.weight
		}]

		Constraints: [ for c in tg.constraints {
			LTarget: c.attribute
			RTarget: c.value
			Operand: c.operator
		}]

		Spreads: [ for s in tg.spreads {
			Attribute:    s.attribute
			Weight:       s.weight
			SpreadTarget: [ for t in s.target {
				Value:   t.value
				Percent: t.percent
			}]
		}]

		if tg.reschedule != null {
			ReschedulePolicy: {
				Attempts:      tg.reschedule.attempts
				DelayFunction: tg.reschedule.delay_function
				if tg.reschedule.delay != _|_ {
					Delay: time.ParseDuration(tg.reschedule.delay)
				}
				if tg.reschedule.interval != _|_ {
					Interval: time.ParseDuration(tg.reschedule.interval)
				}
				if tg.reschedule.max_delay != _|_ {
					MaxDelay: time.ParseDuration(tg.reschedule.max_delay)
				}
				Unlimited: tg.reschedule.unlimited
			}
		}

		if tg.ephemeral_disk != null {
			EphemeralDisk: {
				SizeMB:  tg.ephemeral_disk.size
				Migrate: tg.ephemeral_disk.migrate
				Sticky:  tg.ephemeral_disk.sticky
			}
		}

		if tg.restart_policy != null {
			RestartPolicy: {
				Interval: time.ParseDuration(tg.restart_policy.interval)
				Attempts: tg.restart_policy.attempts
				Delay:    time.ParseDuration(tg.restart_policy.delay)
				Mode:     tg.restart_policy.mode
			}
		}

		// only one network can be specified at group level, and we never use
		// deprecated task level ones.
		if tg.network != null {
			Networks: [{
				Mode: tg.network.mode
				ReservedPorts: [
					for nName, nValue in tg.network.port if nValue.static != null {
						Label:       nName
						Value:       nValue.static
						To:          nValue.to
						HostNetwork: nValue.host_network
					}]
				DynamicPorts: [
					for nName, nValue in tg.network.port if nValue.static == null {
						Label:       nName
						Value:       nValue.static
						To:          nValue.to
						HostNetwork: nValue.host_network
					}]
			}]
		}

		Restart: {
			Attempts: tg.restart.attempts
			Delay:    time.ParseDuration(tg.restart.delay)
			Interval: time.ParseDuration(tg.restart.interval)
			Mode:     tg.restart.mode
		}

		Services: [ for sName, s in tg.service {
			Name:        sName
			TaskName:    s.task
			Tags:        s.tags
			AddressMode: s.address_mode
			if s.check_restart != null {
				CheckRestart: {
					Limit:          s.check_restart.limit
					Grace:          time.ParseDuration(s.check_restart.grace)
					IgnoreWarnings: s.check_restart.ignore_warnings
				}
			}
			Checks: [ for cName, c in s.check {
				{
					AddressMode:            c.address_mode
					Type:                   c.type
					PortLabel:              c.port
					Interval:               time.ParseDuration(c.interval)
					if c.type == "http" {
						Path:     c.path
						Method:   c.method
						Protocol: c.protocol
					}
					Timeout:                time.ParseDuration(c.timeout)
					SuccessBeforePassing:   c.success_before_passing
					FailuresBeforeCritical: c.failures_before_critical
					TLSSkipVerify:          c.tls_skip_verify
					InitialStatus:          c.initial_status
					Header:                 c.header
					Body:                   c.body
					if c.check_restart != null {
						CheckRestart: {
							Limit:          c.check_restart.limit
							Grace:          time.ParseDuration(c.check_restart.grace)
							IgnoreWarnings: c.check_restart.ignore_warnings
						}
					}
				}
			}]
			PortLabel: s.port
			Meta:      s.meta
		}]

		Tasks: [ for tName, t in tg.task {
			Name:       tName
			Driver:     t.driver
			Config:     t.config
			Env:        t.env
			KillSignal: t.kill_signal
			if t.kill_timeout != null {
				KillTimeout: time.ParseDuration(t.kill_timeout)
			}

			Affinities: [ for a in t.affinities {
				LTarget: a.attribute
				RTarget: a.value
				Operand: a.operator
				Weight:  a.weight
			}]

			Constraints: [ for c in t.constraints {
				LTarget: c.attribute
				RTarget: c.value
				Operand: c.operator
			}]

			if t.logs != null {
				LogConfig: {
					MaxFiles:      t.logs.max_files
					MaxFileSizeMB: t.logs.max_file_size
				}
			}

			if t.restart_policy != null {
				RestartPolicy: {
					Interval: time.ParseDuration(t.restart_policy.interval)
					Attempts: t.restart_policy.attempts
					Delay:    time.ParseDuration(t.restart_policy.delay)
					Mode:     t.restart_policy.mode
				}
			}

			if t.lifecycle != null {
				Lifecycle: {
					Hook:    t.lifecycle.hook
					Sidecar: t.lifecycle.sidecar
				}
			}

			Resources: {
				CPU:      t.resources.cpu
				MemoryMB: t.resources.memory
			}

			Templates: [ for tplName, tpl in t.template {
				DestPath:     tplName
				EmbeddedTmpl: tpl.data
				SourcePath:   tpl.source
				Envvars:      tpl.env
				ChangeMode:   tpl.change_mode
				ChangeSignal: tpl.change_signal
				Perms:        tpl.perms
				LeftDelim:    tpl.left_delimiter
				RightDelim:   tpl.right_delimiter
			}]

			Artifacts: [ for artName, art in t.artifact {
				GetterHeaders: art.headers
				GetterMode:    art.mode
				GetterOptions: art.options
				GetterSource:  art.source
				RelativeDest:  artName
			}]

			if t.vault != null {
				Vault: {
					ChangeMode:   t.vault.change_mode
					ChangeSignal: t.vault.change_signal
					Env:          t.vault.env
					Namespace:    t.vault.namespace
					Policies:     t.vault.policies
				}
			}

			VolumeMounts: [ for volName, vol in t.volume_mount {
				Destination:     vol.destination
				PropagationMode: "private"
				ReadOnly:        vol.read_only
				Volume:          volName
			}]
		}]

		if tg.vault != null {
			Vault: {
				ChangeMode:   tg.vault.change_mode
				ChangeSignal: tg.vault.change_signal
				Env:          tg.vault.env
				Namespace:    tg.vault.namespace
				Policies:     tg.vault.policies
			}
		}

		for volName, vol in tg.volume {
			Volumes: "\(volName)": {
				Name:     volName
				Type:     vol.type
				Source:   vol.source
				ReadOnly: vol.read_only
				if vol.type == "csi" {
					MountOptions: {
						FsType:     vol.mount_options.fs_type
						mountFlags: vol.mount_options.mount_flags
					}
				}
			}
		}
	}]
}


// Definitions for stanzas referenced throughout this file
#stanza: {
	job: {
		datacenters: list.MinItems(1)
		namespace:   string
		type:        "batch" | *"service" | "system"
		affinities:  [...#stanza.affinity]
		constraints: [...#stanza.constraint]
		spreads:     [...#stanza.spread]
		group:       [string]: #stanza.group & {#type: type}
		update:      #stanza.update | *null
		vault:       #stanza.vault | *null
		priority:    uint | *50
	}

	affinity: {
		LTarget: string | *null
		RTarget: string
		Operand: "regexp" | "set_contains_all" | "set_contains" | "set_contains_any" | *"=" | "==" | "is" | "!=" | "not" | ">" | ">=" | "<" | "<=" | "version"
		Weight:  uint & !=0 & >=-100 & <=100
	}

	constraint: {
		attribute: string | *null
		value:     string
		operator:  *"=" | "!=" | ">" | ">=" | "<" | "<=" | "distinct_hosts" | "distinct_property" | "regexp" | "set_contains" | "version" | "semver" | "is_set" | "is_not_set"
	}

	spread: {
		attribute: string | *null
		weight:    uint & >=-100 & <=100 | *null
		target:    [...#stanza.targetElem]
	}

	targetElem: {
		value:   string | *null
		percent: uint & >=0 & <=100 | *null
	}

	ephemeral_disk: *null | {
		size:    uint & >0
		migrate: bool | *false
		sticky:  bool | *false
	}

	group: {
		#type:          "service" | "batch" | "system"
		affinities:     [...#stanza.affinity]
		constraints:    [...#stanza.constraint]
		spreads:        [...#stanza.spread]
		ephemeral_disk: #stanza.ephemeral_disk
		network:        *null | #stanza.network
		service:        [string]: #stanza.service
		task:           [string]: #stanza.task
		count:          uint | *1
		volume:         [string]: #stanza.volume
		restart:        #stanza.restart & {#type: #type}
		vault:          *null | #stanza.vault
		restart_policy: *null | #stanza.restart_policy
		reschedule:     #stanza.reschedule & {#type: #type}
	}

	reschedule: {
		#type: "batch" | *"service" | "system"

		if #type == "batch" {
			attempts:       uint | *1
			delay:          #duration | *"5s"
			delay_function: *"constant" | "exponential" | "fibonacci"
			interval:       #duration | *"24h"
			unlimited:      bool | *false
		}

		if #type == "service" || #type == "system" {
			interval:       #duration | *"0m"
			attempts:       uint | *0
			delay:          #duration | *"30s"
			delay_function: "constant" | *"exponential" | "fibonacci"
			max_delay:      #duration | *"1h"
			// if unlimited is true, interval and attempts are ignored
			unlimited:      bool | *true
		}
	}

	network: {
		mode: "host" | "bridge"
		dns:  *null | {
			servers: [...string]
		}
		port: [string]: {
			static:       *null | uint
			to:           *null | uint
			host_network: *"" | string
		}
	}

	restart: {
		#type: "batch" | *"service" | "system"

		// Specifies the number of restarts allowed in the configured interval.
		attempts: uint

		// Specifies the duration to wait before restarting a task. This is
		// specified using a label suffix like "30s" or "1h". A random jitter of up
		// to 25% is added to the delay.
		delay: #duration | *"15s"

		// Specifies the duration which begins when the first task starts and
		// ensures that only attempts number of restarts happens within it. If more
		// than attempts number of failures happen, behavior is controlled by mode.
		// This is specified using a label suffix like "30s" or "1h".
		interval: #duration

		// Controls the behavior when the task fails more than attempts times in an
		// interval.
		mode: *"fail" | "delay"

		if #type == "batch" {
			attempts: uint | *3
			interval: #duration | *"24h"
		}

		if #type == "service" || #type == "system" {
			attempts: uint | *2
			interval: #duration | *"30m"
		}
	}

	check_restart: *null | {
		limit:           uint
		grace:           #duration
		ignore_warnings: bool | *false
	}

	service: {
		check_restart: #stanza.check_restart | *null
		port:          string
		address_mode:  "alloc" | "driver" | *"auto" | "host"
		tags:          [...string]
		task:          string | *""
		check:         [string]: #stanza.check
		meta:          [string]:  string
	}

	check: {
		address_mode:             "alloc" | "driver" | *"host"
		type:                     "http" | "tcp" | "script" | "grpc"
		port:                     string
		interval:                 #duration
		timeout:                  #duration
		check_restart:            #stanza.check_restart | *null
		header:                   [string]: [...string]
		body:                     string | *null
		initial_status:           "passing" | "warning" | "critical" | *""
		success_before_passing:   uint | *0
		failures_before_critical: uint | *0
		tls_skip_verify:          bool | *false

		if type == "http" {
			method:          *"GET" | "POST"
			path:            string
			protocol:        *"http" | "https"
		}

		if type != "http" {
			method:          ""
			path:            ""
			protocol:        ""
		}
	}

	taskConfig: dockerConfig | execConfig

	execConfig: {
		flake:   string
		command: string
		args:    [...string]
	}

	#label: [string]: string

	dockerConfig: {
		image: string
		command: *null | string
		args: [...string]
		cap_add: *null | [...string]
		entrypoint: *null | [...string]
		interactive: *null | bool
		ipc_mode: *null | string
		labels: [...#label]
		logging: dockerConfigLogging
		ports: [...string]
		sysctl: *null | [ { [string]: string } ]
	}

	dockerConfigLogging: {
		type:   "journald"
		config: [...dockerConfigLoggingConfig]
	}

	dockerConfigLoggingConfig: {
		tag:    string
		labels: string
	}

	lifecycle: {
		hook:    "prestart" | "poststart" | "poststop"
		sidecar: *null | bool
	}

	logs: {
		max_files:     uint & >0
		max_file_size: uint & >0
	}

	task: {
		affinities:  [...#stanza.affinity]
		constraints: [...#stanza.constraint]

		artifact: [Destination=_]: {
			destination: Destination
			headers: [string]: string
			mode: *"any" | "file" | "dir"
			options: [string]: string
			source: string
		}

		if driver == "docker" {
			config: #stanza.dockerConfig
		}

		if driver == "exec" {
			config: #stanza.execConfig
		}

		driver: "exec" | "docker" | "nspawn"

		env: [string]: string

		kill_signal: string | *"SIGINT"
		if driver == "docker" {
			kill_signal: "SIGTERM"
		}

		kill_timeout: *null | #duration

		lifecycle: *null | #stanza.lifecycle

		logs: *null | #stanza.logs

		resources: {
			cpu:    uint & >=100
			memory: uint & >=32
		}

		restart: #stanza.restart & {#type: #type}

		template: [Destination=_]: {
			destination:     Destination
			data:            *"" | string
			source:          *"" | string
			env:             bool | *false
			change_mode:     *"restart" | "noop" | "signal"
			change_signal:   *"" | string
			perms:           *"0644" | =~"^[0-7]{4}$"
			left_delimiter:  string | *"{{"
			right_delimiter: string | *"}}"
			splay:           #duration | *"3s"
		}

		vault: *null | #stanza.vault
		volume_mount: [string]: #stanza.volume_mount
		restart_policy: *null | #stanza.restart_policy
	}

	restart_policy: {
		interval: #duration
		attempts: uint
		delay:    #duration
		mode:     "delay" | "fail"
	}

	update: {
		auto_promote:      bool | *false
		auto_revert:       bool | *false
		canary:            uint | *0
		health_check:      *"checks" | "task_states" | "manual"
		healthy_deadline:  #duration | *"5m"
		max_parallel:      uint | *1
		min_healthy_time:  #duration | *"10s"
		progress_deadline: #duration | *"10m"
		stagger:           #duration | *"30s"
	}

	vault: {
		change_mode:   "noop" | *"restart" | "signal"
		change_signal: string | *""
		env:           bool | *true
		namespace:     string | *""
		policies:      [...string]
	}

	volume: {
		type:      "host" | "csi"
		source:    string
		read_only: bool | *false
		if type == "csi" {
			mount_options: {
				fs_type:     *null | string
				mount_flags: *null | string
			}
		}
	}

	volume_mount: {
		// Specifies the group volume that the mount is going to access.
		volume: string | *""

		// Specifies where the volume should be mounted inside the task's
		// allocation.
		destination: string | *""

		// When a group volume is writeable, you may specify that it is read_only
		// on a per mount level using the read_only option here.
		read_only: bool | *false
	}
}
