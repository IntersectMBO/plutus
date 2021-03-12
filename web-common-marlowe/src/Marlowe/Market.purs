module Marlowe.Market (contractTemplates) where

-- At some point we will want to keep contract templates in a database. In the
-- meantime, this is a simple solution to get things up and running.
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Market.Contract1 as Contract1
import Marlowe.Market.Contract2 as Contract2
import Marlowe.Market.Contract3 as Contract3
import Marlowe.Market.Contract4 as Contract4
import Marlowe.Market.Contract5 as Contract5
import Marlowe.Market.Contract6 as Contract6

contractTemplates :: Array ContractTemplate
contractTemplates =
  [ Contract1.contractTemplate
  , Contract2.contractTemplate
  , Contract3.contractTemplate
  , Contract4.contractTemplate
  , Contract5.contractTemplate
  , Contract6.contractTemplate
  ]
