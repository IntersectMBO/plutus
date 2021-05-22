

SET statement_timeout = 0;
SET lock_timeout = 0;
SET idle_in_transaction_session_timeout = 0;
SET client_encoding = 'UTF8';
SET standard_conforming_strings = on;
SELECT pg_catalog.set_config('search_path', '', false);
SET check_function_bodies = false;
SET xmloption = content;
SET client_min_messages = warning;
SET row_security = off;


CREATE SCHEMA fakepab;


ALTER SCHEMA fakepab OWNER TO fakepab;


CREATE EXTENSION IF NOT EXISTS pgcrypto WITH SCHEMA fakepab;



CREATE FUNCTION fakepab.get_or_create_money_container_id_from_pubkey(target_pub_key character varying) RETURNS bigint
    LANGUAGE plpgsql
    AS $$
DECLARE mcid money_container.money_container_id%TYPE;
BEGIN

SELECT w.money_container_id INTO mcid
  FROM wallet w
 WHERE pub_key = target_pub_key;

IF mcid IS NULL THEN
  WITH mc_insert AS (INSERT INTO money_container DEFAULT VALUES
				     RETURNING money_container_id AS id),
   wallet_insert AS (INSERT INTO wallet (money_container_id, pub_key)
					 VALUES ((SELECT id FROM mc_insert), target_pub_key))
		INSERT INTO currency_amount (amount, money_container_id, currency_symbol, token_name)
		VALUES (1000000000, (SELECT id FROM mc_insert), '', '')
		RETURNING money_container_id INTO mcid;
END IF;

RETURN mcid;

END;
$$;


ALTER FUNCTION fakepab.get_or_create_money_container_id_from_pubkey(target_pub_key character varying) OWNER TO fakepab;


CREATE FUNCTION fakepab.process_transaction(target_transaction_id bigint) RETURNS boolean
    LANGUAGE plpgsql
    AS $$
DECLARE

tcontract_id bigint;
told_contract text;
told_state text;
tnew_contract text;
tnew_state text;

min_amount bigint;

BEGIN

IF tcontract_id IS NOT NULL THEN
  SELECT contract_id, old_contract, old_state, new_contract, new_state
  INTO tcontract_id, told_contract, told_state, tnew_contract, tnew_state
  FROM transaction
  WHERE transaction_id = target_transaction_id;

  IF NOT update_contract_if_state_matches(tcontract_id, told_contract, told_state, tnew_contract, tnew_state) THEN
    UPDATE transaction
	SET reason_invalid = 'Old contract state doesn''t match'
	WHERE transaction_id = target_transaction_id;
	RETURN FALSE;
  END IF;
END IF;

SELECT MIN(tl.amount_change + COALESCE(ca.amount, 0))
INTO min_amount
FROM transaction_line tl LEFT OUTER JOIN currency_amount ca
    ON tl.money_container_id = ca.money_container_id
    AND tl.currency_symbol = ca.currency_symbol
    AND tl.token_name = ca.token_name
WHERE transaction_id = target_transaction_id;

IF min_amount < 0
THEN
    UPDATE transaction
	SET reason_invalid = 'Not enough funds'
	WHERE transaction_id = target_transaction_id;
	RETURN FALSE;
ELSE
  INSERT INTO currency_amount (money_container_id, currency_symbol, token_name, amount)
  (SELECT tl.money_container_id AS money_container_id, tl.currency_symbol AS currency_symbol, tl.token_name AS token_name, tl.amount_change + COALESCE(ca.amount, 0) AS amount
   FROM transaction_line tl LEFT OUTER JOIN currency_amount ca
    ON tl.money_container_id = ca.money_container_id
    AND tl.currency_symbol = ca.currency_symbol
    AND tl.token_name = ca.token_name
   WHERE transaction_id = target_transaction_id)
  ON CONFLICT (money_container_id, currency_symbol, token_name)
  DO UPDATE SET amount = EXCLUDED.amount;
  RETURN TRUE;
END IF;

END;
$$;


ALTER FUNCTION fakepab.process_transaction(target_transaction_id bigint) OWNER TO fakepab;


CREATE FUNCTION fakepab.update_contract_if_state_matches(contract_id bigint, old_contract text, old_state text, new_contract text, new_state text) RETURNS boolean
    LANGUAGE plpgsql
    AS $$
DECLARE
  actual_old_contract text;
  actual_old_state text;
BEGIN
  IF contract_id IS NULL THEN
    RETURN TRUE;
  ELSE
	SELECT contract, state
	INTO actual_old_contract, actual_old_state
	FROM contract
	WHERE money_container_id = contract_id;

	IF contract = actual_old_contract AND state = actual_old_state THEN
	  UPDATE contract
	  SET contract = new_contract, state = new_state
      WHERE money_container_id = contract_id;

      RETURN TRUE;
	ELSE
      RETURN FALSE;
	END IF;
  END IF;
END;
$$;


ALTER FUNCTION fakepab.update_contract_if_state_matches(contract_id bigint, old_contract text, old_state text, new_contract text, new_state text) OWNER TO fakepab;

SET default_tablespace = '';


CREATE TABLE fakepab.contract (
    money_container_id bigint NOT NULL,
    contract text,
    state text,
    currency_symbol character varying(70) NOT NULL,
    original_contract text,
    original_state text
);


ALTER TABLE fakepab.contract OWNER TO fakepab;


CREATE TABLE fakepab.currency_amount (
    amount numeric NOT NULL,
    money_container_id bigint NOT NULL,
    currency_symbol character varying(70) NOT NULL,
    token_name character varying(70) NOT NULL,
    CONSTRAINT positive_currency_amount CHECK ((amount >= (0)::numeric))
);


ALTER TABLE fakepab.currency_amount OWNER TO fakepab;


CREATE TABLE fakepab.currency_symbol (
    currency_symbol character varying(70) NOT NULL
);


ALTER TABLE fakepab.currency_symbol OWNER TO fakepab;


CREATE TABLE fakepab.money_container (
    money_container_id bigint NOT NULL
);


ALTER TABLE fakepab.money_container OWNER TO fakepab;


CREATE SEQUENCE fakepab.money_container_money_container_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MINVALUE
    NO MAXVALUE
    CACHE 1;


ALTER TABLE fakepab.money_container_money_container_id_seq OWNER TO fakepab;


ALTER SEQUENCE fakepab.money_container_money_container_id_seq OWNED BY fakepab.money_container.money_container_id;



CREATE TABLE fakepab.slot (
    slot_number bigint NOT NULL,
    slot_time timestamp without time zone DEFAULT CURRENT_TIMESTAMP NOT NULL,
    is_settled boolean DEFAULT false NOT NULL
);


ALTER TABLE fakepab.slot OWNER TO fakepab;


CREATE SEQUENCE fakepab.slot_slot_number_seq
    START WITH 1
    INCREMENT BY 1
    NO MINVALUE
    NO MAXVALUE
    CACHE 1;


ALTER TABLE fakepab.slot_slot_number_seq OWNER TO fakepab;


ALTER SEQUENCE fakepab.slot_slot_number_seq OWNED BY fakepab.slot.slot_number;



CREATE TABLE fakepab.token (
    currency_symbol character varying(70) NOT NULL,
    token_name character varying(70) NOT NULL
);


ALTER TABLE fakepab.token OWNER TO fakepab;


CREATE TABLE fakepab.transaction (
    transaction_id bigint NOT NULL,
    slot_number bigint,
    contract_id bigint,
    signing_wallet_id bigint NOT NULL,
    inputs text,
    state_before text,
    state_after text,
    contract_before text,
    contract_after text,
    reason_invalid text
);


ALTER TABLE fakepab.transaction OWNER TO fakepab;


CREATE TABLE fakepab.transaction_line (
    transaction_id bigint NOT NULL,
    line_num bigint NOT NULL,
    money_container_id bigint NOT NULL,
    amount_change numeric NOT NULL,
    currency_symbol character varying(70) NOT NULL,
    token_name character varying(70) NOT NULL
);


ALTER TABLE fakepab.transaction_line OWNER TO fakepab;


CREATE VIEW fakepab.transaction_pool AS
 SELECT transaction.transaction_id,
    transaction.slot_number,
    transaction.contract_id,
    transaction.signing_wallet_id,
    transaction.inputs,
    transaction.state_before,
    transaction.state_after,
    transaction.contract_before,
    transaction.contract_after,
    transaction.reason_invalid
   FROM fakepab.transaction
  WHERE ((transaction.slot_number IS NULL) AND (transaction.reason_invalid IS NULL));


ALTER TABLE fakepab.transaction_pool OWNER TO fakepab;


CREATE SEQUENCE fakepab.transaction_transaction_id_seq
    START WITH 1
    INCREMENT BY 1
    NO MINVALUE
    NO MAXVALUE
    CACHE 1;


ALTER TABLE fakepab.transaction_transaction_id_seq OWNER TO fakepab;


ALTER SEQUENCE fakepab.transaction_transaction_id_seq OWNED BY fakepab.transaction.transaction_id;



CREATE TABLE fakepab.wallet (
    money_container_id bigint NOT NULL,
    pub_key character varying(70) NOT NULL
);


ALTER TABLE fakepab.wallet OWNER TO fakepab;


ALTER TABLE ONLY fakepab.money_container ALTER COLUMN money_container_id SET DEFAULT nextval('fakepab.money_container_money_container_id_seq'::regclass);



ALTER TABLE ONLY fakepab.slot ALTER COLUMN slot_number SET DEFAULT nextval('fakepab.slot_slot_number_seq'::regclass);



ALTER TABLE ONLY fakepab.transaction ALTER COLUMN transaction_id SET DEFAULT nextval('fakepab.transaction_transaction_id_seq'::regclass);



SELECT pg_catalog.setval('fakepab.money_container_money_container_id_seq', 1, false);



SELECT pg_catalog.setval('fakepab.slot_slot_number_seq', 1, false);



SELECT pg_catalog.setval('fakepab.transaction_transaction_id_seq', 1, false);



ALTER TABLE ONLY fakepab.currency_amount
    ADD CONSTRAINT currency_amount_pkey PRIMARY KEY (money_container_id, currency_symbol, token_name);



ALTER TABLE ONLY fakepab.currency_symbol
    ADD CONSTRAINT currency_symbol_pkey PRIMARY KEY (currency_symbol);



ALTER TABLE ONLY fakepab.contract
    ADD CONSTRAINT currency_symbol_unique UNIQUE (currency_symbol);



ALTER TABLE ONLY fakepab.contract
    ADD CONSTRAINT money_container_id PRIMARY KEY (money_container_id);



ALTER TABLE ONLY fakepab.money_container
    ADD CONSTRAINT money_container_pkey PRIMARY KEY (money_container_id);



ALTER TABLE ONLY fakepab.slot
    ADD CONSTRAINT slot_pkey PRIMARY KEY (slot_number);



ALTER TABLE ONLY fakepab.token
    ADD CONSTRAINT token_pkey PRIMARY KEY (currency_symbol, token_name);



ALTER TABLE ONLY fakepab.transaction_line
    ADD CONSTRAINT transaction_line_pkey PRIMARY KEY (transaction_id, line_num);



ALTER TABLE ONLY fakepab.transaction
    ADD CONSTRAINT transaction_pkey PRIMARY KEY (transaction_id);



ALTER TABLE ONLY fakepab.wallet
    ADD CONSTRAINT wallet_pkey PRIMARY KEY (money_container_id);



ALTER TABLE ONLY fakepab.wallet
    ADD CONSTRAINT wallet_pub_key_key UNIQUE (pub_key);



CREATE UNIQUE INDEX index_contract_currency_symbol ON fakepab.contract USING btree (currency_symbol);



CREATE INDEX index_currency_amount_money_container_id ON fakepab.currency_amount USING btree (money_container_id);



CREATE INDEX index_currency_amount_token ON fakepab.currency_amount USING btree (currency_symbol, token_name);



CREATE UNIQUE INDEX index_pub_key ON fakepab.wallet USING btree (pub_key);



CREATE INDEX index_transaction_contract_id ON fakepab.transaction USING btree (contract_id);



CREATE INDEX index_transaction_line_money_container_id ON fakepab.transaction_line USING btree (money_container_id);



CREATE INDEX index_transaction_line_token ON fakepab.transaction_line USING btree (currency_symbol, token_name);



CREATE INDEX index_transaction_signing_wallet_id ON fakepab.transaction USING btree (signing_wallet_id);



CREATE INDEX index_transaction_slot ON fakepab.transaction USING btree (slot_number);



ALTER TABLE ONLY fakepab.currency_amount
    ADD CONSTRAINT currency_amount_currency_symbol_fkey FOREIGN KEY (currency_symbol, token_name) REFERENCES fakepab.token(currency_symbol, token_name);



ALTER TABLE ONLY fakepab.currency_amount
    ADD CONSTRAINT currency_amount_money_container_id_fkey FOREIGN KEY (money_container_id) REFERENCES fakepab.money_container(money_container_id);



ALTER TABLE ONLY fakepab.contract
    ADD CONSTRAINT fk_contract_currency_symbol FOREIGN KEY (currency_symbol) REFERENCES fakepab.currency_symbol(currency_symbol);



ALTER TABLE ONLY fakepab.contract
    ADD CONSTRAINT fk_contract_money_container FOREIGN KEY (money_container_id) REFERENCES fakepab.money_container(money_container_id);



ALTER TABLE ONLY fakepab.transaction
    ADD CONSTRAINT fk_transaction_slot FOREIGN KEY (transaction_id) REFERENCES fakepab.slot(slot_number);



ALTER TABLE ONLY fakepab.transaction
    ADD CONSTRAINT fk_transaction_wallet FOREIGN KEY (signing_wallet_id) REFERENCES fakepab.wallet(money_container_id);



ALTER TABLE ONLY fakepab.wallet
    ADD CONSTRAINT fk_wallet_money_container FOREIGN KEY (money_container_id) REFERENCES fakepab.money_container(money_container_id) NOT VALID;



ALTER TABLE ONLY fakepab.token
    ADD CONSTRAINT token_currency_symbol FOREIGN KEY (currency_symbol) REFERENCES fakepab.currency_symbol(currency_symbol) NOT VALID;



ALTER TABLE ONLY fakepab.transaction
    ADD CONSTRAINT transaction_contract_id_fkey FOREIGN KEY (contract_id) REFERENCES fakepab.contract(money_container_id) NOT VALID;



ALTER TABLE ONLY fakepab.transaction_line
    ADD CONSTRAINT transaction_line_currency_symbol_fkey FOREIGN KEY (currency_symbol, token_name) REFERENCES fakepab.token(currency_symbol, token_name);



ALTER TABLE ONLY fakepab.transaction_line
    ADD CONSTRAINT transaction_line_money_container_id_fkey FOREIGN KEY (money_container_id) REFERENCES fakepab.money_container(money_container_id);



ALTER TABLE ONLY fakepab.transaction_line
    ADD CONSTRAINT transaction_line_transaction_id_fkey FOREIGN KEY (transaction_id) REFERENCES fakepab.transaction(transaction_id);


INSERT INTO fakepab.currency_symbol (currency_symbol) VALUES ('');
INSERT INTO fakepab.token (currency_symbol, token_name) VALUES ('', '');


GRANT ALL ON SCHEMA fakepab TO fakepab;



