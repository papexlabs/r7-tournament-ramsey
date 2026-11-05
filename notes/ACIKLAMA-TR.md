# R(7) ≤ 46: ispatın sade anlatımı

Bu not, sonucu kendi ağzından anlatabilmen ve gelebilecek sorulara cevap verebilmen için hazırlandı. Teknik ayrıntılar makalede ve `notes/FEASIBILITY.md` dosyasında.

## 1. Soru

**Turnuva.** Her oyuncunun diğer her oyuncuyla tam bir kez oynadığı ve beraberliğin olmadığı bir lig düşün. Kim kimi yendiyse, oradan bir ok çizilir. Matematikte buna turnuva denir.

**Tam sıralı grup (TT_k).** k oyuncudan oluşan bir grup düşün. Birincisi diğer herkesi yenmiş, ikincisi kendinden sonra gelen herkesi yenmiş ve sonuncuya kadar böyle gidiyor. Yani grubun içindeki maçlarda hiç sürpriz yok. Buna "geçişli alt turnuva" denir ve TT_k diye yazılır.

**R(k).** Erdős ile Moser'in 1964'te sorduğu soru şu: kaç oyunculu her turnuvada mutlaka k kişilik tam sıralı bir grup bulunur? Bu sayıya R(k) denir.

**Bilinenler:**
- Küçük değerler biliniyor. En son bulunan R(6) = 28; bunu Sanchez-Flores 1994'te gösterdi.
- 2022'de Neiman, Mackey ve Heule 34 ≤ R(7) ≤ 47 olduğunu gösterdi. 34'ten küçük olamayacağını, 47'den büyük olamayacağını ispatladılar. Not boyunca bu makaleye kısaca "2022 makalesi" diyorum.

**Bizim sonuç:** 46 oyunculu her turnuvada da 7 kişilik tam sıralı bir grup vardır. Yani R(7) ≤ 46 ve bilinen aralık 34–46'ya daralıyor.

## 2. İspatın fikri

Kanıt tersine işler. Diyelim ki 46 oyunculu, içinde 7 kişilik tam sıralı grup olmayan bir turnuva var. Bunun imkânsız olduğunu göstereceğiz.

**Bir oyuncu seç: v.** Diğer 45 oyuncu iki gruba ayrılır:
- v'yi **yenenler** (giriş grubu);
- v'nin **yendikleri** (çıkış grubu).

**Önemli gözlem:** Bu gruplardan hiçbiri kendi içinde 6 kişilik tam sıralı grup içeremez.
- Giriş grubunda böyle 6 kişi olsaydı, hepsi v'yi yenmiş olurdu. v'yi en sona koyunca 7 kişilik tam sıralı bir grup çıkardı.
- Çıkış grubunda olsaydı, v hepsini yenmiş olurdu. v'yi en başa koyunca yine 7 kişi çıkardı.
- R(6) = 28 olduğu için iki grubun her biri en fazla 27 kişidir.

**Durumlar:** Giriş grubunun büyüklüğüne bakıyoruz. İki grubun toplamı her zaman 45.

1. **Giriş grubu 26 ya da daha fazla kişi.** 26 kişilik ve 6'lı tam sıralı grup içermeyen tek bir turnuva var (ST26). Çıkış grubu da en az 18 kişi, dolayısıyla içinde 5 kişilik tam sıralı bir grup var. "ST26 + v + 5'li grup" yapısının 7'li içermeden tamamlanamayacağı bilgisayarla gösterildi. Bu durum imkânsız.
2. **Giriş grubu tam 25 kişi.** Bu boyutta da tek bir yapı var (ST25). Çıkış grubu 20 kişi. 20 kişilik her turnuvada iki özel küçük yapıdan biri (H6 ya da W7) bulunur. İki birleşim için de bilgisayar "olmaz" diyor.
3. **Ayna simetrisi.** Bütün okları ters çevirirsek "yenen" ile "yenilen" yer değiştirir; aynı mantık çıkış grubu için de geçerli olur. Geriye yalnızca iki durum kalıyor: giriş grubu 24 ve çıkış grubu 21, ya da giriş grubu 23 ve çıkış grubu 22. Diğer iki dağılım bunların aynası.
4. **(23, 22) durumu.** 23 kişilik "6'lı içermeyen" turnuvaların tam 25 çeşidi var. 2022 makalesi her birinin karşısına Y8 adlı 8 kişilik küçük bir yapı konunca 7'li çıkmadan tamamlanamayacağını gösterdi. Bu 25 hesaptan oluşuyor. **Bizim yeni katkımız:** 22 kişilik "6'lı içermeyen" bütün turnuvaları (89 çeşit) eksiksiz listeledik ve hepsinin içinde Y8 olduğunu gösterdik. Böylece bu durum, hiç yeni hesap yapmadan kapanıyor.
5. **(24, 21) durumu.** 2022 makalesi tam burada takılmıştı.
   - 21 kişilik "6'lı içermeyen" bütün turnuvaları listeledik: 17.040 çeşit.
   - Bunlardan 17.039'u Y8 içeriyor. Onlar da 4. maddedeki 25 hesapla kapanıyor, çünkü 24 kişilik grubun içinden 23 kişilik bir parça seçilebilir.
   - Tek bir istisna var. Ona **O21*** dedik: çok simetrik, tamamen dengeli, Y8 içermeyen 21 kişilik bir turnuva.
   - 24 kişilik "6'lı içermeyen" turnuvaların 5 çeşidi var. Her birinin O21* ile birleşip birleşemeyeceğini tek tek kontrol etmek gerekiyordu.
   - Bunlar 5 büyük hesap: her birinde 46 oyuncu ve oku belirsiz 504 maç var. Bu hesapları biz yaptık (Aşama 3). Beşi de "olmaz" çıktı.

Hiçbir durum mümkün olmadığına göre, 46 oyunculu ve 7'li tam sıralı grup içermeyen bir turnuva yoktur.

## 3. Bilgisayar ne yaptı, neden güveniyoruz

**SAT çözücü.** Her "olmaz" sonucu bir SAT çözücüden geliyor. Soru mantık formüllerine çevrilir ve çözücü "bu formülü sağlayan bir atama var mı?" diye arar. Bulamazsa cevap UNSAT, yani "imkânsız" olur.

**Kanıt dosyası.** Çözücünün "bulamadım" demesi yetmez, çünkü çözücüde hata olabilir. Bu yüzden çözücü her adımını bir kanıt dosyasına yazar (LRAT biçiminde). Bu dosyayı, çözücüden bağımsız, çok küçük ve basit bir kontrol programı baştan sona doğrular. Kontrol programı "geçerli" demeden hiçbir parça kapanmış sayılmadı.

**Parçalara bölme.** Büyük hesaplar binlerce parçaya bölündü. Zor parçalar daha da küçük parçalara bölündü. Ayrıca parçaların bütün olasılıkları eksiksiz kapsadığı da kontrol edildi.

**Rakamlar:**
- **Aşama 3** (yeni hesaplar): 48.995 parça, hepsi kanıtlı UNSAT.
- **Aşama 4** (2022 makalesinin 28 hesabının yeniden yapılması): 31.942 parça, hepsi kanıtlı UNSAT. 2022 makalesi kanıt dosyası yayımlamamıştı. Artık onların hesapları da kanıtlı.
- **Aşama 1–2** (listeler): 21, 22, 23, 24 ve 25 kişilik bütün "6'lı içermeyen" turnuvaların listesi kanıtlı olarak yeniden çıkarıldı. Sonuç, Lohn, Lambert ve Heule'nin 2022'de yöntem açıklamadan yayımladığı dosyalarla birebir aynı çıktı.

**Bütün ispat bunlara dayanıyor:**
1. Literatürdeki bazı teoremler: R(6) = 28, R(5) = 14, 26 kişilik yapının tekliği ve 2022 makalesindeki küçük bir yardımcı önerme. Hangilerini kendimiz yeniden doğruladık, hangilerini kaynağa dayanarak kullanıyoruz; bağımsız denetimden sonra kesinleştirip makalede tek tek yazacağım.
2. Yukarıdaki durum ayrımının doğru olması.
3. Formüllerin soruyu doğru ifade etmesi. Bunun için ayrı bir doğrulama programı var.
4. Kanıt kontrol programının doğru olması. Bu program küçük ve yaygın kullanılan bir araç.

## 4. Gelebilecek sorular

**"Bilgisayar hata yapmış olamaz mı?"**
Çözücünün kendisine güvenmiyoruz, her sonucu ayrı bir programla doğruladık. Kanıt dosyaları ve kod açık olacak; herkes kendi bilgisayarında tekrar kontrol edebilir.

**"Neden yalnızca bu durumlar yetiyor?"**
2. bölümdeki durum ayrımı bütün dağılımları kapsıyor. Tek bir oyuncunun giriş ve çıkış gruplarına bakmak yeterli.

**"2022'dekiler neden 46'ya inmedi?"**
(24, 21) ve (23, 22) durumları açık kalmıştı. Makalelerinde, 20 kişinin üstündeki "6'lı içermeyen" turnuvaların tam listesinin işe yarayabileceğini yazmışlardı. Biz bu listeleri kanıtlı olarak çıkardık. Listede tek istisna olan O21* sayesinde iş 5 hesaba indi.

**"45'e inebilir misiniz?"**
Bilmiyoruz. 45'te durumlar çok daha fazla ve aynı yöntem doğrudan yetmiyor. Bu açık bir soru.

**"AI ne yaptı?"**
- Hesap altyapısını, kodlamayı ve kontrol programlarını kurdu.
- Bulut sunucularını yönetti.
- Sonuçları denetledi ve makalenin ilk taslağını yazdı.
- Kararlar ve sorumluluk sende. AI yazar olarak listelenmiyor, rolü makalede açıkça yazıyor.

**"Bu ne kadar tuttu?"**
- Toplam ~4.900 işlemci-saat hesap. Kaba toplam: listeler + Aşama 3'te ~2.600 + Aşama 4'te ~1.150 + kayıplar.
- AWS maliyeti ~39 $.
