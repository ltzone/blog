git pull origin master
npm install
npm run build
if [ $? -ne 0 ]; then
    echo "build failed"
else
    rm -rf ~/www
    mkdir ~/www
    cp -R docs/.vuepress/dist/* ~/www
fi