// Widget de combustíveis para a app Scriptable (iPhone)
// 1) Instala a app "Scriptable" (gratuita) na App Store.
// 2) Cria um script novo, cola este código e guarda.
// 3) No ecrã principal: adiciona um widget do Scriptable, toca nele, escolhe este script.
//
// Ajusta o combustível aqui: "Gasóleo simples", "Gasóleo especial / plus",
// "Gasolina 95 simples", "Gasolina 95 especial / plus", "Gasolina 98" ou "GPL".
const COMBUSTIVEL = "Gasóleo simples";
const ROTULO = "Gasóleo";
const URL_DADOS = "https://rodrigoosv.github.io/combustiveis-/dados.json";

async function carregar() {
  const pedido = new Request(URL_DADOS + "?t=" + Date.now());
  pedido.timeoutInterval = 15;
  return await pedido.loadJSON();
}

const widget = new ListWidget();
widget.backgroundColor = Color.dynamic(new Color("#ffffff"), new Color("#1c1c1e"));
widget.url = "https://rodrigoosv.github.io/combustiveis-/";
widget.refreshAfterDate = new Date(Date.now() + 30 * 60 * 1000);

try {
  const dados = await carregar();
  const g = dados.grupos[COMBUSTIVEL];
  if (!g) throw new Error("Combustível sem dados");

  const titulo = widget.addText("Mais barato · " + ROTULO);
  titulo.font = Font.semiboldSystemFont(12);
  titulo.textColor = Color.gray();

  widget.addSpacer(4);
  const preco = widget.addText(g.mais_barato.preco_texto + " €");
  preco.font = Font.boldSystemFont(34);
  preco.textColor = Color.dynamic(Color.black(), Color.white());
  preco.minimumScaleFactor = 0.6;

  widget.addSpacer(2);
  const posto = widget.addText(g.mais_barato.posto);
  posto.font = Font.semiboldSystemFont(14);
  posto.textColor = new Color("#007aff");
  posto.lineLimit = 1;

  widget.addSpacer();
  const media = widget.addText("Média " + String(g.media.toFixed(3)).replace(".", ",") + " € · " + dados.atualizado.slice(5, 16).replace("-", "/"));
  media.font = Font.systemFont(10);
  media.textColor = Color.gray();
  media.lineLimit = 1;
} catch (e) {
  const erro = widget.addText("Sem dados.\nVerifica a ligação.");
  erro.font = Font.systemFont(13);
  erro.textColor = Color.gray();
}

if (config.runsInWidget) {
  Script.setWidget(widget);
} else {
  await widget.presentSmall();
}
Script.complete();
