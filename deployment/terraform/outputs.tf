output "plutus_rest_api_id" {
  value = "${aws_api_gateway_rest_api.plutus.id}"
}

output "marlowe_rest_api_id" {
  value = "${aws_api_gateway_rest_api.marlowe.id}"
}

output "region" {
  value = "${var.aws_region}"
}