module Marlowe.Contracts where

depositInsentive :: String
depositInsentive = """CommitCash (IdentCC 1) 1
           (ConstMoney 100)
           10 200
           (CommitCash (IdentCC 2) 2
                       (ConstMoney 20)
                       20 200
                       (When (PersonChoseSomething (IdentChoice 1) 1)
                             100
                             (Both (RedeemCC (IdentCC 1) Null)
                                   (RedeemCC (IdentCC 2) Null))
                             (Pay (IdentPay 1) 2 1
                                  (ConstMoney 20)
                                  200
                                  (Both (RedeemCC (IdentCC 1) Null)
                                        (RedeemCC (IdentCC 2) Null))))
                       (RedeemCC (IdentCC 1) Null))
           Null
"""

crowdFunding :: String
crowdFunding = """Both (Both (Both (When (AndObs (PersonChoseSomething (IdentChoice 1) 1)
                               (ValueGE (MoneyFromChoice (IdentChoice 1) 1
                                                         (ConstMoney 0))
                                        (ConstMoney 1)))
                       10
                       (CommitCash (IdentCC 1) 1
                                   (MoneyFromChoice (IdentChoice 1) 1
                                                    (ConstMoney 0))
                                   10 20 Null Null)
                       Null)
                 (When (AndObs (PersonChoseSomething (IdentChoice 2) 2)
                               (ValueGE (MoneyFromChoice (IdentChoice 2) 2
                                                         (ConstMoney 0))
                                        (ConstMoney 1)))
                       10
                       (CommitCash (IdentCC 2) 2
                                   (MoneyFromChoice (IdentChoice 2) 2
                                                    (ConstMoney 0))
                                   10 20 Null Null)
                       Null))
           (Both (When (AndObs (PersonChoseSomething (IdentChoice 3) 3)
                               (ValueGE (MoneyFromChoice (IdentChoice 3) 3
                                                         (ConstMoney 0))
                                        (ConstMoney 1)))
                       10
                       (CommitCash (IdentCC 3) 3
                                   (MoneyFromChoice (IdentChoice 3) 3
                                                    (ConstMoney 0))
                                   10 20 Null Null)
                       Null)
                 (When (AndObs (PersonChoseSomething (IdentChoice 4) 4)
                               (ValueGE (MoneyFromChoice (IdentChoice 4) 4
                                                         (ConstMoney 0))
                                        (ConstMoney 1)))
                       10
                       (CommitCash (IdentCC 4) 4
                                   (MoneyFromChoice (IdentChoice 4) 4
                                                    (ConstMoney 0))
                                   10 20 Null Null)
                       Null)))
     (When FalseObs 10 Null
           (Choice (ValueGE (AddMoney (AddMoney (AvailableMoney (IdentCC 1))
                                                (AvailableMoney (IdentCC 2)))
                                      (AddMoney (AvailableMoney (IdentCC 3))
                                                (AvailableMoney (IdentCC 4))))
                            (ConstMoney 1000))
                   (Both (Both (Pay (IdentPay 1) 1 5
                                    (AvailableMoney (IdentCC 1))
                                    20 Null)
                               (Pay (IdentPay 2) 2 5
                                    (AvailableMoney (IdentCC 2))
                                    20 Null))
                         (Both (Pay (IdentPay 3) 3 5
                                    (AvailableMoney (IdentCC 3))
                                    20 Null)
                               (Pay (IdentPay 4) 4 5
                                    (AvailableMoney (IdentCC 4))
                                    20 Null)))
                   Null))
"""

escrow :: String
escrow = """CommitCash (IdentCC 1) 1
           (ConstMoney 450)
           10 100
           (When (OrObs (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 0)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 0)
                                              (PersonChoseThis (IdentChoice 3) 3 0)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 0)
                                       (PersonChoseThis (IdentChoice 3) 3 0)))
                        (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                              (PersonChoseThis (IdentChoice 3) 3 1)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                       (PersonChoseThis (IdentChoice 3) 3 1))))
                 90
                 (Choice (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                        (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                               (PersonChoseThis (IdentChoice 3) 3 1)))
                                (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                        (PersonChoseThis (IdentChoice 3) 3 1)))
                         (Pay (IdentPay 1) 1 2
                              (AvailableMoney (IdentCC 1))
                              100
                              (RedeemCC (IdentCC 1) Null))
                         (RedeemCC (IdentCC 1) Null))
                 (RedeemCC (IdentCC 1) Null))
           Null
"""