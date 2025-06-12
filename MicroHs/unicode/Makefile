UNICODE_VERSION=16.0.0
.PHONY: clean

all: uni_string

uni_string:	UniParse UnicodeData.txt
	echo "unicodeVersion :: Version" > uni_string
	echo $(UNICODE_VERSION) | sed -e 's/\./,/g' -e 's/^/unicodeVersion = makeVersion [/' -e 's/$$/]/' >> uni_string
	./UniParse >> uni_string

UniParse: UniParse.hs
	mhs UniParse.hs -oUniParse

UnicodeData.txt:
	wget https://www.unicode.org/Public/$(UNICODE_VERSION)/ucd/UnicodeData.txt

DerivedCoreProperties.txt:
	wget https://www.unicode.org/Public/$(UNICODE_VERSION)/ucd/DerivedCoreProperties.txt

clean:
	rm -rf UnicodeData.txt DerivedCoreProperties.txt UniParse uni_string
