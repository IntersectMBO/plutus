locals {
  monitoring_domain_name = "${var.monitoring_full_domain != "" ? var.monitoring_full_domain : "${var.env}.${var.monitoring_tld}"}"
  github_webhook_domain_name = "github.${var.env}.${var.monitoring_tld}"
  meadow_domain_name = "${var.meadow_full_domain != "" ? var.meadow_full_domain : "${var.env}.${var.meadow_tld}"}"
  plutus_domain_name = "${var.plutus_full_domain != "" ? var.plutus_full_domain : "${var.env}.${var.plutus_tld}"}"
}

