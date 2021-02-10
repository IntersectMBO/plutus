locals {
  monitoring_domain_name = "${var.monitoring_full_domain != "" ? var.monitoring_full_domain : "${var.env}.${var.monitoring_tld}"}"
  github_webhook_domain_name = "github.${var.env}.${var.monitoring_tld}"
  marlowe_dash_domain_name = "${var.env}.${var.marlowe_dash_tld}"
  marlowe_domain_name = "${var.marlowe_full_domain != "" ? var.marlowe_full_domain : "${var.env}.${var.marlowe_tld}"}"
  plutus_domain_name = "${var.plutus_full_domain != "" ? var.plutus_full_domain : "${var.env}.${var.plutus_tld}"}"
}

