import express from 'express'
import puppeteer from 'puppeteer'
import browserSync from "browser-sync"
import chokidar from "chokidar"
import exporter from "./exporter.js"

// Start browserSync server
const bs = browserSync.create();
bs.init({ 
    files: [ "dev.html", "cheatsheet.pdf" ],
    server: {
        baseDir: "./",
        index: "dev.html"
    }
});

// Initialize puppeteer
const puppeteerServerPort = 8080;
const puppeteerServerUrl = `http://localhost:${puppeteerServerPort}/`;
const puppeteerServer = new Promise((resolve) => {
    const app = express();
    app.use(express.static('./'));
    const server = app.listen(puppeteerServerPort, () => resolve(server));
});
const puppeteerBrowser = puppeteerServer.then(() => puppeteer.launch());

// Initialize build watcher
const buildFileWatcher = chokidar.watch([
    "indice.json",
    "*.md",
    "immagini/**/*",
    "stile.css"
]);
buildFileWatcher.on('change', async path => {
    console.log(`File ${path} has been changed`);

    await exporter(puppeteerServerUrl, await puppeteerBrowser);
    console.log(`Exported cheatsheet.pdf`);

    bs.reload("cheatsheet.pdf");
});