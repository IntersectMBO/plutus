module BenchUtil.RefData
    (
    -- string
      rdLoremIpsum1
    , rdLoremIpsum5
    , rdFoundationEn
    , rdFoundationZh
    , rdFoundationJap
    , rdFoundationHun
    , rdFoundationLower
    , rdFoundationUpper
    , rdSpecialCasing
    -- byte array
    , rdBytes20
    , rdBytes200
    , rdBytes2000
    , rdWord32
    ) where

import Prelude (Int, Char, cycle, take, ($))
import Data.Word (Word8, Word32)

rdLoremIpsum1 :: [Char]
rdLoremIpsum1 = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nam ornare dui vitae porta varius. In quis diam sed felis elementum ultricies non sit amet lorem. Nullam ut erat varius lectus scelerisque iaculis sed eu leo. Vivamus gravida interdum elit suscipit tempus. Quisque at mauris ac sapien consequat feugiat. In varius interdum rhoncus. Etiam hendrerit pharetra consectetur. Pellentesque laoreet, nisi quis feugiat rhoncus, nisi ipsum tincidunt nulla, vel fermentum mauris nisl sed felis. Sed ac convallis nibh. Donec rutrum finibus odio et rhoncus. Suspendisse pulvinar ex ac fermentum fermentum. Nam dui dui, lobortis sit amet sapien sed, gravida sagittis magna. Vestibulum nec egestas dui, non efficitur lectus. Fusce vitae mattis sem, nec dignissim nibh. Sed ac tincidunt metus."

rdLoremIpsum5 :: [Char]
rdLoremIpsum5 = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nam ornare dui vitae porta varius. In quis diam sed felis elementum ultricies non sit amet lorem. Nullam ut erat varius lectus scelerisque iaculis sed eu leo. Vivamus gravida interdum elit suscipit tempus. Quisque at mauris ac sapien consequat feugiat. In varius interdum rhoncus. Etiam hendrerit pharetra consectetur. Pellentesque laoreet, nisi quis feugiat rhoncus, nisi ipsum tincidunt nulla, vel fermentum mauris nisl sed felis. Sed ac convallis nibh. Donec rutrum finibus odio et rhoncus. Suspendisse pulvinar ex ac fermentum fermentum. Nam dui dui, lobortis sit amet sapien sed, gravida sagittis magna. Vestibulum nec egestas dui, non efficitur lectus. Fusce vitae mattis sem, nec dignissim nibh. Sed ac tincidunt metus.  Vestibulum ac bibendum ex. In vulputate pellentesque elementum. Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos himenaeos. Maecenas elit libero, vehicula eget hendrerit non, convallis vel metus. Maecenas faucibus nulla id quam vestibulum, eget commodo tellus interdum. Mauris eu odio id lacus gravida sollicitudin. Aenean vel velit enim. Phasellus vitae urna nisl. Interdum et malesuada fames ac ante ipsum primis in faucibus. Nunc volutpat convallis elementum.  Curabitur suscipit congue ligula non maximus. Fusce tristique lacinia sem sed condimentum. Sed non eleifend mi, fringilla congue tortor. Nunc rhoncus sit amet nisl ac tempor. Fusce sed consectetur purus, et aliquam sem. Vestibulum finibus lectus et vehicula euismod. Aliquam sed neque mattis, sollicitudin enim sed, vestibulum est. Quisque varius pharetra risus id tempor. In hac habitasse platea dictumst. Donec cursus nisi sed magna bibendum aliquet. Mauris a elit id erat imperdiet consequat. Phasellus at condimentum ipsum. Pellentesque vehicula pulvinar ipsum et porta. Nullam quis quam mauris. Sed scelerisque porta nibh eu tempor. Morbi sollicitudin fringilla sollicitudin.  Cras nec velit quis velit sollicitudin pellentesque. Phasellus quis ullamcorper nisi. Curabitur fringilla sed turpis sit amet pharetra. Cras euismod eget massa eu posuere. Suspendisse id aliquam enim. Nullam sollicitudin aliquet elementum. Nulla sit amet ligula vitae lorem finibus laoreet sed ac velit. Nulla facilisi. Aenean vel pretium lectus. Nunc augue lorem, viverra et felis vel, vestibulum feugiat nisl. Vestibulum imperdiet laoreet posuere. Maecenas vestibulum consequat felis eu aliquam. Nullam ac efficitur ante, eget egestas mauris. Cras id tincidunt nisi. Cras tincidunt molestie lorem et bibendum.  Donec commodo porttitor faucibus. Aenean aliquam suscipit iaculis. Cras eu purus sit amet elit rhoncus laoreet. Vestibulum fringilla nulla ut neque vestibulum porttitor. Pellentesque vitae risus elit. Quisque et sapien eu diam tincidunt luctus ac quis nunc. Proin nec nisl eget diam faucibus tempus id sed quam. Ut scelerisque enim lacus, at mollis diam sagittis et. Nam lobortis convallis maximus. Donec maximus tortor id consequat venenatis."

rdFoundationEn :: [Char]
rdFoundationEn = "Set in the year 0 F.E. (\"Foundation Era\"), The Psychohistorians opens on Trantor, the capital of the 12,000-year-old Galactic Empire. Though the empire appears stable and powerful, it is slowly decaying in ways that parallel the decline of the Western Roman Empire. Hari Seldon, a mathematician and psychologist, has developed psychohistory, a new field of science and psychology that equates all possibilities in large societies to mathematics, allowing for the prediction of future events."

rdFoundationLower :: [Char]
rdFoundationLower = "set in the year 0 f.e. (\"foundation era\"), the psychohistorians opens on trantor, the capital of the 12,000-year-old galactic empire. though the empire appears stable and powerful, it is slowly decaying in ways that parallel the decline of the western roman empire. hari seldon, a mathematician and psychologist, has developed psychohistory, a new field of science and psychology that equates all possibilities in large societies to mathematics, allowing for the prediction of future events."

rdFoundationUpper :: [Char]
rdFoundationUpper = "SET IN THE YEAR 0 F.E. (\"FOUNDATION ERA\"), THE PSYCHOHISTORIANS OPENS ON TRANTOR, THE CAPITAL OF THE 12,000-YEAR-OLD GALACTIC EMPIRE. THOUGH THE EMPIRE APPEARS STABLE AND POWERFUL, IT IS SLOWLY DECAYING IN WAYS THAT PARALLEL THE DECLINE OF THE WESTERN ROMAN EMPIRE. HARI SELDON, A MATHEMATICIAN AND PSYCHOLOGIST, HAS DEVELOPED PSYCHOHISTORY, A NEW FIELD OF SCIENCE AND PSYCHOLOGY THAT EQUATES ALL POSSIBILITIES IN LARGE SOCIETIES TO MATHEMATICS, ALLOWING FOR THE PREDICTION OF FUTURE EVENTS."

rdFoundationZh :: [Char]
rdFoundationZh = "故事發生在〈心理史學家〉五十年後，端點星面臨首度的「謝頓危機」（Seldon Crisis）銀河帝國邊緣的星群紛紛獨立起來，端點星處於四個王國之間，備受威脅。此時，謝頓早前錄下影像突然播放，告知他的後人端點星「銀河百科全書第一號基地」的真正目的──在千年後建立一個新的銀河帝國。同時，在這一千年間，基地會遇到各種不同的危機，令基地可以急速成長。端點星市長塞佛·哈定（Salvor Hardin）趁機發動政變，從心神未定的百科全書理事會手中奪權，以他靈活的手腕帶領端點星走出危機。"

rdFoundationHun :: [Char]
rdFoundationHun = "A történet G.K. 12 067-ben (A.K. 1) játszódik. A fiatal és tehetséges matematikus, Gaal Dornick a Trantorra, a Galaktikus Birodalom központi bolygójára tart, hogy csatlakozzon egy tekintélyes matematikus, I. Cleon császár egykori első minisztere, Hari Seldon tervezetéhez, a Seldon-tervhez. Gaal nem sokat tud a terv mibenlétéről, ám Seldon személyes meghívásának hatására a Trantorra indul. Megérkezése után nem sokkal találkozik Seldonnal, aki elmondja neki, hogy a tervet és az azzal kapcsolatba hozható személyeket – így őt is – a Közbiztonsági Bizottság – a Birodalomban a császárral szemben a tényleges hatalmat gyakorló testület –, szigorú megfigyelés alatt tart. Seldon beszél Gaal-nak a terv néhány részletéről, és megemlíti, hogy Trantor a pszichohistóriai számítások szerint 500 éven belül elpusztul. Találkozásuk másnapján Gaal-t és Seldon-t is letartóztatják."

rdFoundationJap :: [Char]
rdFoundationJap = "数学者ハリ・セルダンは、膨大な集団の行動を予測する心理歴史学を作りあげ発展させることで、銀河帝国が近いうちに崩壊することを予言する[1]。セルダンは、帝国崩壊後に3万年続くはずの暗黒時代を、あらゆる知識を保存することで千年に縮めようとし、知識の集大成となる銀河百科事典 (Encyclopedia Galactica) を編纂するグループ「ファウンデーション」をつくったが、帝国崩壊を公言し平和を乱したという罪で裁判にかけられ、グループは銀河系辺縁部にある資源の乏しい無人惑星ターミナスへ追放されることになった。しかし、この追放劇すらもセルダンの計画に予定されていた事柄であった。病で死期をさとっていたセルダンは、己の仕事が終わったことを確信する。"

rdSpecialCasing :: [Char]
rdSpecialCasing = "ﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄ"

rdBytes20 ::[Word8]
rdBytes20 = take 20 $ cycle [1..255]

rdBytes200 :: [Word8]
rdBytes200 = take 200 $ cycle [1..255]

rdBytes2000 :: [Word8]
rdBytes2000 = take 2000 $ cycle [1..255]

rdWord32 :: Int -> [Word32]
rdWord32 n = Prelude.take n $ Prelude.cycle [1..255]
