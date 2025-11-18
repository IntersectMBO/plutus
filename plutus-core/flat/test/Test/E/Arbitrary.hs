{-# LANGUAGE CPP #-}

module Test.E.Arbitrary where

import Test.E
import Test.Tasty.QuickCheck

-- GENERATED START

instance () => Arbitrary E2 where
  arbitrary =
    do
      x <- choose (0 :: Int, 1)
      case x of
        0 -> return E2_1
        1 -> return E2_2
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E3 where
  arbitrary =
    do
      x <- choose (0 :: Int, 2)
      case x of
        0 -> return E3_1
        1 -> return E3_2
        2 -> return E3_3
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E4 where
  arbitrary =
    do
      x <- choose (0 :: Int, 3)
      case x of
        0 -> return E4_1
        1 -> return E4_2
        2 -> return E4_3
        3 -> return E4_4
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E8 where
  arbitrary =
    do
      x <- choose (0 :: Int, 7)
      case x of
        0 -> return E8_1
        1 -> return E8_2
        2 -> return E8_3
        3 -> return E8_4
        4 -> return E8_5
        5 -> return E8_6
        6 -> return E8_7
        7 -> return E8_8
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E16 where
  arbitrary =
    do
      x <- choose (0 :: Int, 15)
      case x of
        0 -> return E16_1
        1 -> return E16_2
        2 -> return E16_3
        3 -> return E16_4
        4 -> return E16_5
        5 -> return E16_6
        6 -> return E16_7
        7 -> return E16_8
        8 -> return E16_9
        9 -> return E16_10
        10 -> return E16_11
        11 -> return E16_12
        12 -> return E16_13
        13 -> return E16_14
        14 -> return E16_15
        15 -> return E16_16
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E17 where
  arbitrary =
    do
      x <- choose (0 :: Int, 16)
      case x of
        0 -> return E17_1
        1 -> return E17_2
        2 -> return E17_3
        3 -> return E17_4
        4 -> return E17_5
        5 -> return E17_6
        6 -> return E17_7
        7 -> return E17_8
        8 -> return E17_9
        9 -> return E17_10
        10 -> return E17_11
        11 -> return E17_12
        12 -> return E17_13
        13 -> return E17_14
        14 -> return E17_15
        15 -> return E17_16
        16 -> return E17_17
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E32 where
  arbitrary =
    do
      x <- choose (0 :: Int, 31)
      case x of
        0 -> return E32_1
        1 -> return E32_2
        2 -> return E32_3
        3 -> return E32_4
        4 -> return E32_5
        5 -> return E32_6
        6 -> return E32_7
        7 -> return E32_8
        8 -> return E32_9
        9 -> return E32_10
        10 -> return E32_11
        11 -> return E32_12
        12 -> return E32_13
        13 -> return E32_14
        14 -> return E32_15
        15 -> return E32_16
        16 -> return E32_17
        17 -> return E32_18
        18 -> return E32_19
        19 -> return E32_20
        20 -> return E32_21
        21 -> return E32_22
        22 -> return E32_23
        23 -> return E32_24
        24 -> return E32_25
        25 -> return E32_26
        26 -> return E32_27
        27 -> return E32_28
        28 -> return E32_29
        29 -> return E32_30
        30 -> return E32_31
        31 -> return E32_32
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

#ifdef ENUM_LARGE
instance () => Arbitrary E256 where
    arbitrary
      = do x <- choose (0 :: Int, 255)
           case x of
               0   -> return E256_1
               1   -> return E256_2
               2   -> return E256_3
               3   -> return E256_4
               4   -> return E256_5
               5   -> return E256_6
               6   -> return E256_7
               7   -> return E256_8
               8   -> return E256_9
               9   -> return E256_10
               10  -> return E256_11
               11  -> return E256_12
               12  -> return E256_13
               13  -> return E256_14
               14  -> return E256_15
               15  -> return E256_16
               16  -> return E256_17
               17  -> return E256_18
               18  -> return E256_19
               19  -> return E256_20
               20  -> return E256_21
               21  -> return E256_22
               22  -> return E256_23
               23  -> return E256_24
               24  -> return E256_25
               25  -> return E256_26
               26  -> return E256_27
               27  -> return E256_28
               28  -> return E256_29
               29  -> return E256_30
               30  -> return E256_31
               31  -> return E256_32
               32  -> return E256_33
               33  -> return E256_34
               34  -> return E256_35
               35  -> return E256_36
               36  -> return E256_37
               37  -> return E256_38
               38  -> return E256_39
               39  -> return E256_40
               40  -> return E256_41
               41  -> return E256_42
               42  -> return E256_43
               43  -> return E256_44
               44  -> return E256_45
               45  -> return E256_46
               46  -> return E256_47
               47  -> return E256_48
               48  -> return E256_49
               49  -> return E256_50
               50  -> return E256_51
               51  -> return E256_52
               52  -> return E256_53
               53  -> return E256_54
               54  -> return E256_55
               55  -> return E256_56
               56  -> return E256_57
               57  -> return E256_58
               58  -> return E256_59
               59  -> return E256_60
               60  -> return E256_61
               61  -> return E256_62
               62  -> return E256_63
               63  -> return E256_64
               64  -> return E256_65
               65  -> return E256_66
               66  -> return E256_67
               67  -> return E256_68
               68  -> return E256_69
               69  -> return E256_70
               70  -> return E256_71
               71  -> return E256_72
               72  -> return E256_73
               73  -> return E256_74
               74  -> return E256_75
               75  -> return E256_76
               76  -> return E256_77
               77  -> return E256_78
               78  -> return E256_79
               79  -> return E256_80
               80  -> return E256_81
               81  -> return E256_82
               82  -> return E256_83
               83  -> return E256_84
               84  -> return E256_85
               85  -> return E256_86
               86  -> return E256_87
               87  -> return E256_88
               88  -> return E256_89
               89  -> return E256_90
               90  -> return E256_91
               91  -> return E256_92
               92  -> return E256_93
               93  -> return E256_94
               94  -> return E256_95
               95  -> return E256_96
               96  -> return E256_97
               97  -> return E256_98
               98  -> return E256_99
               99  -> return E256_100
               100 -> return E256_101
               101 -> return E256_102
               102 -> return E256_103
               103 -> return E256_104
               104 -> return E256_105
               105 -> return E256_106
               106 -> return E256_107
               107 -> return E256_108
               108 -> return E256_109
               109 -> return E256_110
               110 -> return E256_111
               111 -> return E256_112
               112 -> return E256_113
               113 -> return E256_114
               114 -> return E256_115
               115 -> return E256_116
               116 -> return E256_117
               117 -> return E256_118
               118 -> return E256_119
               119 -> return E256_120
               120 -> return E256_121
               121 -> return E256_122
               122 -> return E256_123
               123 -> return E256_124
               124 -> return E256_125
               125 -> return E256_126
               126 -> return E256_127
               127 -> return E256_128
               128 -> return E256_129
               129 -> return E256_130
               130 -> return E256_131
               131 -> return E256_132
               132 -> return E256_133
               133 -> return E256_134
               134 -> return E256_135
               135 -> return E256_136
               136 -> return E256_137
               137 -> return E256_138
               138 -> return E256_139
               139 -> return E256_140
               140 -> return E256_141
               141 -> return E256_142
               142 -> return E256_143
               143 -> return E256_144
               144 -> return E256_145
               145 -> return E256_146
               146 -> return E256_147
               147 -> return E256_148
               148 -> return E256_149
               149 -> return E256_150
               150 -> return E256_151
               151 -> return E256_152
               152 -> return E256_153
               153 -> return E256_154
               154 -> return E256_155
               155 -> return E256_156
               156 -> return E256_157
               157 -> return E256_158
               158 -> return E256_159
               159 -> return E256_160
               160 -> return E256_161
               161 -> return E256_162
               162 -> return E256_163
               163 -> return E256_164
               164 -> return E256_165
               165 -> return E256_166
               166 -> return E256_167
               167 -> return E256_168
               168 -> return E256_169
               169 -> return E256_170
               170 -> return E256_171
               171 -> return E256_172
               172 -> return E256_173
               173 -> return E256_174
               174 -> return E256_175
               175 -> return E256_176
               176 -> return E256_177
               177 -> return E256_178
               178 -> return E256_179
               179 -> return E256_180
               180 -> return E256_181
               181 -> return E256_182
               182 -> return E256_183
               183 -> return E256_184
               184 -> return E256_185
               185 -> return E256_186
               186 -> return E256_187
               187 -> return E256_188
               188 -> return E256_189
               189 -> return E256_190
               190 -> return E256_191
               191 -> return E256_192
               192 -> return E256_193
               193 -> return E256_194
               194 -> return E256_195
               195 -> return E256_196
               196 -> return E256_197
               197 -> return E256_198
               198 -> return E256_199
               199 -> return E256_200
               200 -> return E256_201
               201 -> return E256_202
               202 -> return E256_203
               203 -> return E256_204
               204 -> return E256_205
               205 -> return E256_206
               206 -> return E256_207
               207 -> return E256_208
               208 -> return E256_209
               209 -> return E256_210
               210 -> return E256_211
               211 -> return E256_212
               212 -> return E256_213
               213 -> return E256_214
               214 -> return E256_215
               215 -> return E256_216
               216 -> return E256_217
               217 -> return E256_218
               218 -> return E256_219
               219 -> return E256_220
               220 -> return E256_221
               221 -> return E256_222
               222 -> return E256_223
               223 -> return E256_224
               224 -> return E256_225
               225 -> return E256_226
               226 -> return E256_227
               227 -> return E256_228
               228 -> return E256_229
               229 -> return E256_230
               230 -> return E256_231
               231 -> return E256_232
               232 -> return E256_233
               233 -> return E256_234
               234 -> return E256_235
               235 -> return E256_236
               236 -> return E256_237
               237 -> return E256_238
               238 -> return E256_239
               239 -> return E256_240
               240 -> return E256_241
               241 -> return E256_242
               242 -> return E256_243
               243 -> return E256_244
               244 -> return E256_245
               245 -> return E256_246
               246 -> return E256_247
               247 -> return E256_248
               248 -> return E256_249
               249 -> return E256_250
               250 -> return E256_251
               251 -> return E256_252
               252 -> return E256_253
               253 -> return E256_254
               254 -> return E256_255
               255 -> return E256_256
               _   -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E258 where
    arbitrary
      = do x <- choose (0 :: Int, 257)
           case x of
               0   -> return E258_1
               1   -> return E258_2
               2   -> return E258_3
               3   -> return E258_4
               4   -> return E258_5
               5   -> return E258_6
               6   -> return E258_7
               7   -> return E258_8
               8   -> return E258_9
               9   -> return E258_10
               10  -> return E258_11
               11  -> return E258_12
               12  -> return E258_13
               13  -> return E258_14
               14  -> return E258_15
               15  -> return E258_16
               16  -> return E258_17
               17  -> return E258_18
               18  -> return E258_19
               19  -> return E258_20
               20  -> return E258_21
               21  -> return E258_22
               22  -> return E258_23
               23  -> return E258_24
               24  -> return E258_25
               25  -> return E258_26
               26  -> return E258_27
               27  -> return E258_28
               28  -> return E258_29
               29  -> return E258_30
               30  -> return E258_31
               31  -> return E258_32
               32  -> return E258_33
               33  -> return E258_34
               34  -> return E258_35
               35  -> return E258_36
               36  -> return E258_37
               37  -> return E258_38
               38  -> return E258_39
               39  -> return E258_40
               40  -> return E258_41
               41  -> return E258_42
               42  -> return E258_43
               43  -> return E258_44
               44  -> return E258_45
               45  -> return E258_46
               46  -> return E258_47
               47  -> return E258_48
               48  -> return E258_49
               49  -> return E258_50
               50  -> return E258_51
               51  -> return E258_52
               52  -> return E258_53
               53  -> return E258_54
               54  -> return E258_55
               55  -> return E258_56
               56  -> return E258_57
               57  -> return E258_58
               58  -> return E258_59
               59  -> return E258_60
               60  -> return E258_61
               61  -> return E258_62
               62  -> return E258_63
               63  -> return E258_64
               64  -> return E258_65
               65  -> return E258_66
               66  -> return E258_67
               67  -> return E258_68
               68  -> return E258_69
               69  -> return E258_70
               70  -> return E258_71
               71  -> return E258_72
               72  -> return E258_73
               73  -> return E258_74
               74  -> return E258_75
               75  -> return E258_76
               76  -> return E258_77
               77  -> return E258_78
               78  -> return E258_79
               79  -> return E258_80
               80  -> return E258_81
               81  -> return E258_82
               82  -> return E258_83
               83  -> return E258_84
               84  -> return E258_85
               85  -> return E258_86
               86  -> return E258_87
               87  -> return E258_88
               88  -> return E258_89
               89  -> return E258_90
               90  -> return E258_91
               91  -> return E258_92
               92  -> return E258_93
               93  -> return E258_94
               94  -> return E258_95
               95  -> return E258_96
               96  -> return E258_97
               97  -> return E258_98
               98  -> return E258_99
               99  -> return E258_100
               100 -> return E258_101
               101 -> return E258_102
               102 -> return E258_103
               103 -> return E258_104
               104 -> return E258_105
               105 -> return E258_106
               106 -> return E258_107
               107 -> return E258_108
               108 -> return E258_109
               109 -> return E258_110
               110 -> return E258_111
               111 -> return E258_112
               112 -> return E258_113
               113 -> return E258_114
               114 -> return E258_115
               115 -> return E258_116
               116 -> return E258_117
               117 -> return E258_118
               118 -> return E258_119
               119 -> return E258_120
               120 -> return E258_121
               121 -> return E258_122
               122 -> return E258_123
               123 -> return E258_124
               124 -> return E258_125
               125 -> return E258_126
               126 -> return E258_127
               127 -> return E258_128
               128 -> return E258_129
               129 -> return E258_130
               130 -> return E258_131
               131 -> return E258_132
               132 -> return E258_133
               133 -> return E258_134
               134 -> return E258_135
               135 -> return E258_136
               136 -> return E258_137
               137 -> return E258_138
               138 -> return E258_139
               139 -> return E258_140
               140 -> return E258_141
               141 -> return E258_142
               142 -> return E258_143
               143 -> return E258_144
               144 -> return E258_145
               145 -> return E258_146
               146 -> return E258_147
               147 -> return E258_148
               148 -> return E258_149
               149 -> return E258_150
               150 -> return E258_151
               151 -> return E258_152
               152 -> return E258_153
               153 -> return E258_154
               154 -> return E258_155
               155 -> return E258_156
               156 -> return E258_157
               157 -> return E258_158
               158 -> return E258_159
               159 -> return E258_160
               160 -> return E258_161
               161 -> return E258_162
               162 -> return E258_163
               163 -> return E258_164
               164 -> return E258_165
               165 -> return E258_166
               166 -> return E258_167
               167 -> return E258_168
               168 -> return E258_169
               169 -> return E258_170
               170 -> return E258_171
               171 -> return E258_172
               172 -> return E258_173
               173 -> return E258_174
               174 -> return E258_175
               175 -> return E258_176
               176 -> return E258_177
               177 -> return E258_178
               178 -> return E258_179
               179 -> return E258_180
               180 -> return E258_181
               181 -> return E258_182
               182 -> return E258_183
               183 -> return E258_184
               184 -> return E258_185
               185 -> return E258_186
               186 -> return E258_187
               187 -> return E258_188
               188 -> return E258_189
               189 -> return E258_190
               190 -> return E258_191
               191 -> return E258_192
               192 -> return E258_193
               193 -> return E258_194
               194 -> return E258_195
               195 -> return E258_196
               196 -> return E258_197
               197 -> return E258_198
               198 -> return E258_199
               199 -> return E258_200
               200 -> return E258_201
               201 -> return E258_202
               202 -> return E258_203
               203 -> return E258_204
               204 -> return E258_205
               205 -> return E258_206
               206 -> return E258_207
               207 -> return E258_208
               208 -> return E258_209
               209 -> return E258_210
               210 -> return E258_211
               211 -> return E258_212
               212 -> return E258_213
               213 -> return E258_214
               214 -> return E258_215
               215 -> return E258_216
               216 -> return E258_217
               217 -> return E258_218
               218 -> return E258_219
               219 -> return E258_220
               220 -> return E258_221
               221 -> return E258_222
               222 -> return E258_223
               223 -> return E258_224
               224 -> return E258_225
               225 -> return E258_226
               226 -> return E258_227
               227 -> return E258_228
               228 -> return E258_229
               229 -> return E258_230
               230 -> return E258_231
               231 -> return E258_232
               232 -> return E258_233
               233 -> return E258_234
               234 -> return E258_235
               235 -> return E258_236
               236 -> return E258_237
               237 -> return E258_238
               238 -> return E258_239
               239 -> return E258_240
               240 -> return E258_241
               241 -> return E258_242
               242 -> return E258_243
               243 -> return E258_244
               244 -> return E258_245
               245 -> return E258_246
               246 -> return E258_247
               247 -> return E258_248
               248 -> return E258_249
               249 -> return E258_250
               250 -> return E258_251
               251 -> return E258_252
               252 -> return E258_253
               253 -> return E258_254
               254 -> return E258_255
               255 -> return E258_256
               256 -> return E258_257
               257 -> return E258_258
               _   -> error "FATAL ERROR: Arbitrary instance, logic bug"
-- GENERATED STOP
#endif
