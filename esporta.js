import express from 'express'
import puppeteer from 'puppeteer'
import exporter from "./exporter.js"

const numeroPorta = 8080;
const url = `http://localhost:${numeroPorta}/`;

const app = express();
app.use(express.static('./'));

new Promise((resolve) => { const server = app.listen(numeroPorta, () => resolve(server)) })
    .then(server => puppeteer.launch()
        .then(browser => exporter(url, browser)
            .then(() => console.log("Exported cheatsheet.pdf"))
            .then(() => browser.close())
            .then(() => server.close())));