npm install
npm run build
if [ $? -ne 0 ]; then
    echo "build failed"
else
    echo "deploying to server ..."
    ssh ltzhou@ltzhou.com "cd ~; rm -rf wiki; mkdir wiki"
    cd docs/.vuepress/dist; tar -zcf - ./ | ssh ltzhou@ltzhou.com "tar -zxf - -C ~/wiki"
    echo "success"
fi