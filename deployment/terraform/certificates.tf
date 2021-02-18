# Plutus Playground SSL Certificate
resource "aws_acm_certificate" "plutus_private" {
  domain_name      = "*.${var.plutus_tld}"
  validation_method = "DNS"
}

resource "aws_route53_record" "plutus_private" {
  for_each = {
    for dvo in aws_acm_certificate.plutus_private.domain_validation_options : dvo.domain_name => {
      name   = dvo.resource_record_name
      record = dvo.resource_record_value
      type   = dvo.resource_record_type
    }
  }

  allow_overwrite = true
  name            = each.value.name
  records         = [each.value.record]
  ttl             = 60
  type            = each.value.type
  zone_id         = var.plutus_public_zone
}

resource "aws_acm_certificate_validation" "plutus_private" {
  certificate_arn         = aws_acm_certificate.plutus_private.arn
  validation_record_fqdns = [for record in aws_route53_record.plutus_private : record.fqdn]
}


# Marlowe Playground SSL Certificate
resource "aws_acm_certificate" "marlowe_private" {
  domain_name      = "*.${var.marlowe_tld}"
  validation_method = "DNS"
}

resource "aws_route53_record" "marlowe_private" {
  for_each = {
    for dvo in aws_acm_certificate.marlowe_private.domain_validation_options : dvo.domain_name => {
      name   = dvo.resource_record_name
      record = dvo.resource_record_value
      type   = dvo.resource_record_type
    }
  }

  allow_overwrite = true
  name            = each.value.name
  records         = [each.value.record]
  ttl             = 60
  type            = each.value.type
  zone_id         = var.marlowe_public_zone
}

resource "aws_acm_certificate_validation" "marlowe_private" {
  certificate_arn         = aws_acm_certificate.marlowe_private.arn
  validation_record_fqdns = [for record in aws_route53_record.marlowe_private : record.fqdn]
}

# Marlowe Dash SSL Certificate
resource "aws_acm_certificate" "marlowe_dash_private" {
  domain_name      = "*.${var.marlowe_dash_tld}"
  validation_method = "DNS"
}

resource "aws_route53_record" "marlowe_dash_private" {
  for_each = {
    for dvo in aws_acm_certificate.marlowe_dash_private.domain_validation_options : dvo.domain_name => {
      name   = dvo.resource_record_name
      record = dvo.resource_record_value
      type   = dvo.resource_record_type
    }
  }

  allow_overwrite = true
  name            = each.value.name
  records         = [each.value.record]
  ttl             = 60
  type            = each.value.type
  zone_id         = var.marlowe_dash_public_zone
}

resource "aws_acm_certificate_validation" "marlowe_dash_private" {
  certificate_arn         = aws_acm_certificate.marlowe_dash_private.arn
  validation_record_fqdns = [for record in aws_route53_record.marlowe_dash_private : record.fqdn]
}

# Monitoring SSL Certificate
resource "aws_acm_certificate" "monitoring_private" {
  domain_name      = "*.${var.monitoring_tld}"
  validation_method = "DNS"
}

resource "aws_route53_record" "monitoring_private" {
  for_each = {
    for dvo in aws_acm_certificate.monitoring_private.domain_validation_options : dvo.domain_name => {
      name   = dvo.resource_record_name
      record = dvo.resource_record_value
      type   = dvo.resource_record_type
    }
  }

  allow_overwrite = true
  name            = each.value.name
  records         = [each.value.record]
  ttl             = 60
  type            = each.value.type
  zone_id         = var.monitoring_public_zone
}

resource "aws_acm_certificate_validation" "monitoring_private" {
  certificate_arn         = aws_acm_certificate.monitoring_private.arn
  validation_record_fqdns = [for record in aws_route53_record.monitoring_private : record.fqdn]
}