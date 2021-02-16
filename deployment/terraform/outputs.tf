output "plutus_rest_api_id" {
  value = "${aws_api_gateway_rest_api.plutus.id}"
}

output "marlowe_rest_api_id" {
  value = "${aws_api_gateway_rest_api.marlowe.id}"
}

output "region" {
  value = "${var.aws_region}"
}

# output "prometheus_user_data" {
  # value = "${data.template_file.prometheus_user_data.rendered}"
# }