{ config, ... }: {
  services.ingress-config.extraHttpsBackends = ''
    {{ range services -}}
      {{ if .Tags | contains "ingress" -}}
        {{ range service .Name -}}
          {{ if (and (eq .ServiceMeta.IngressBind "*:443") .ServiceMeta.IngressServer) -}}
            use_backend {{ .ID }} if { hdr(host) -i {{ .ServiceMeta.IngressHost }} } {{ .ServiceMeta.IngressIf }}
          {{ end -}}
        {{ end -}}
      {{ end -}}
    {{ end -}}
  '';

  services.ingress-config.extraConfig = ''
    {{ range services -}}
      {{ if .Tags | contains "ingress" -}}
        {{ range service .Name -}}
          {{ if .ServiceMeta.IngressServer -}}
            backend {{ .ID }}
              mode {{ or .ServiceMeta.IngressMode "http" }}
              default-server resolve-prefer ipv4 resolvers consul resolve-opts allow-dup-ip
              {{ .ServiceMeta.IngressBackendExtra }}
              server {{.ID}} {{ .ServiceMeta.IngressServer }}

            {{ if (and .ServiceMeta.IngressBind (ne .ServiceMeta.IngressBind "*:443") ) }}
              frontend {{ .ID }}
                bind {{ .ServiceMeta.IngressBind }}
                mode {{ or .ServiceMeta.IngressMode "http" }}
                default_backend {{ .ID }}
            {{ end }}
          {{ end -}}
        {{ end -}}
      {{ end -}}
    {{ end }}
  '';
}
