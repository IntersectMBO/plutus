# Public ALB

# Security Group
resource "aws_security_group" "public_alb" {
  vpc_id = aws_vpc.plutus.id

  ## inbound (world): ICMP 3:4 "Fragmentation Needed and Don't Fragment was Set"
  ingress {
    from_port   = "3"
    to_port     = "4"
    protocol    = "ICMP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## inbound (world): https
  ingress {
    from_port   = "443"
    to_port     = "443"
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## inbound (world): http
  ingress {
    from_port   = "80"
    to_port     = "80"
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = local.prometheus_port
    to_port     = local.prometheus_port
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  egress {
    from_port   = 80
    to_port     = 80
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  egress {
    from_port   = 8080
    to_port     = 8080
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  tags = {
    Name        = "${local.project}_${var.env}_public_alb"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_alb" "plutus" {
  subnets         = aws_subnet.public.*.id
  security_groups = [aws_security_group.public_alb.id]
  internal        = false

  tags = {
    Name        = "${local.project}_${var.env}_public_alb"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_lb_listener" "redirect" {
  load_balancer_arn = aws_alb.plutus.arn
  port              = "80"
  protocol          = "HTTP"

  default_action {
    type = "redirect"

    redirect {
      port        = "443"
      protocol    = "HTTPS"
      status_code = "HTTP_301"
    }
  }
}

resource "aws_alb_listener" "playground" {
  load_balancer_arn = aws_alb.plutus.arn
  port              = "443"
  protocol          = "HTTPS"
  certificate_arn   = aws_acm_certificate.plutus_private.arn

  default_action {
    target_group_arn = aws_alb_target_group.webghc.arn
    type             = "forward"
  }
}

resource "aws_lb_listener_certificate" "marlowe" {
  listener_arn    = aws_alb_listener.playground.arn
  certificate_arn = aws_acm_certificate.marlowe_private.arn
}

resource "aws_lb_listener_certificate" "monitoring" {
  listener_arn    = aws_alb_listener.playground.arn
  certificate_arn = aws_acm_certificate.monitoring_private.arn
}

resource "aws_lb_listener_certificate" "marlowe_dash" {
  listener_arn    = aws_alb_listener.playground.arn
  certificate_arn = aws_acm_certificate.marlowe_dash_private.arn
}

## ALB rule for web-ghc
resource "aws_alb_target_group" "webghc" {
  # ALB is taking care of SSL termination so we listen to port 80 here
  port     = "80"
  protocol = "HTTP"
  vpc_id   = aws_vpc.plutus.id

  health_check {
    path = "/health"
  }

  stickiness {
    type = "lb_cookie"
  }
}

resource "aws_alb_listener_rule" "runghc" {
  depends_on   = [aws_alb_target_group.webghc]
  # The API Gateway uses http for proxying rather than https so we
  # have to go through the redirect listener to get here
  # If we moved away from API Gateway we would need to use the
  # playground listener instead
  listener_arn = aws_lb_listener.redirect.arn
  priority     = 100

  action {
    type             = "forward"
    target_group_arn = aws_alb_target_group.webghc.id
  }

  condition {
    path_pattern {
      values = ["/runghc"]
    }
  }
}

resource "aws_alb_target_group_attachment" "webghc_a" {
  target_group_arn = aws_alb_target_group.webghc.arn
  target_id        = aws_instance.webghc_a.id
  port             = "80"
}

resource "aws_alb_target_group_attachment" "webghc_b" {
  target_group_arn = aws_alb_target_group.webghc.arn
  target_id        = aws_instance.webghc_b.id
  port             = "80"
}

# Monitoring
resource "aws_alb_target_group" "monitoring" {
  # ALB is taking care of SSL termination so we listen to port 80 here
  port     = "80"
  protocol = "HTTP"
  vpc_id   = aws_vpc.plutus.id

  health_check {
    path = "/metrics"
  }

  stickiness {
    type = "lb_cookie"
  }
}

resource "aws_alb_listener_rule" "monitoring" {
  depends_on   = [aws_alb_target_group.monitoring]
  listener_arn = aws_alb_listener.playground.arn
  priority     = 103

  action {
    type             = "forward"
    target_group_arn = aws_alb_target_group.monitoring.id
  }

  condition {
    host_header {
      values = [local.monitoring_domain_name]
    }
  }
}

resource "aws_alb_target_group_attachment" "monitoring_a" {
  target_group_arn = aws_alb_target_group.monitoring.arn
  target_id        = aws_instance.prometheus.id
  port             = local.prometheus_port
}

resource "aws_route53_record" "monitoring_alb" {
  zone_id = var.monitoring_public_zone
  name    = local.monitoring_domain_name
  type    = "A"

  alias {
    name                   = aws_alb.plutus.dns_name
    zone_id                = aws_alb.plutus.zone_id
    evaluate_target_health = true
  }
}

## ALB rule for marlowe-dashboard
resource "aws_alb_target_group" "marlowe_dash" {
  # ALB is taking care of SSL termination so we listen to port 80 here
  port     = "80"
  protocol = "HTTP"
  vpc_id   = aws_vpc.plutus.id

  health_check {
    path = "/version"
  }

  stickiness {
    type = "lb_cookie"
  }
}

resource "aws_alb_listener_rule" "marlowe_dash" {
  depends_on   = [aws_alb_target_group.marlowe_dash]
  listener_arn = aws_alb_listener.playground.arn
  priority     = 114

  action {
    type             = "forward"
    target_group_arn = aws_alb_target_group.marlowe_dash.id
  }

  condition {
    host_header {
      values = [local.marlowe_dash_domain_name]
    }
  }
}

resource "aws_alb_target_group_attachment" "marlowe_dash_a" {
  target_group_arn = aws_alb_target_group.marlowe_dash.arn
  target_id        = aws_instance.marlowe_dash_a.id
  port             = "8080"
}

# resource "aws_alb_target_group_attachment" "marlowe_dash_b" {
#   target_group_arn = aws_alb_target_group.marlowe_dash.arn
#   target_id        = aws_instance.marlowe_dash_b.id
#   port             = "8080"
# }

resource "aws_route53_record" "marlowe_dash_alb" {
  zone_id = var.marlowe_dash_public_zone
  name    = local.marlowe_dash_domain_name
  type    = "A"

  alias {
    name                   = aws_alb.plutus.dns_name
    zone_id                = aws_alb.plutus.zone_id
    evaluate_target_health = true
  }
}
