---
title: Cloud Server Tips
date: 2021-02-16 12:58:20


sidebar: true
lang: en-US
---


<!-- more -->


## User Auth

1. `adduser`
2. `tee /etc/sudoers.d/ltzhou <<< 'ltzhou ALL=(ALL) ALL'`

## Nginx

Nginx 配置文件结构以及最佳实践

1. 所有的 Nginx 配置文件都在`/etc/nginx/`目录下。
2. 主要的 Nginx 配置文件是`/etc/nginx/nginx.conf`。
3. 为每个域名创建一个独立的配置文件，便于维护服务器。你可以按照需要定义任意多的 block 文件。
4. Nginx 服务器配置文件被储存在`/etc/nginx/sites-available`目录下。在`/etc/nginx/sites-enabled`目录下的配置文件都将被 Nginx 使用。
5. 最佳推荐是使用标准的命名方式。例如，如果你的域名是`mydomain.com`，那么配置文件应该被命名为`/etc/nginx/sites-available/mydomain.com.conf`
6. 如果你在域名服务器配置块中有可重用的配置段，把这些配置段摘出来，做成一小段可重用的配置。
7. Nginx 日志文件(`access.log` 和 `error.log`)定位在`/var/log/nginx/`目录下。推荐为每个服务器配置块，配置一个不同的access和error。
8. 你可以将你的网站根目录设置在任何你想要的地方。最常用的网站根目录位置包括：
   - `/home/<user_name>/<site_name>`
   - `/var/www/<site_name>`
   - `/var/www/html/<site_name>`
   - `/opt/<site_name>`


::: tip
如果要在一个server下部署多个目录，对于非`/`的location，文件地址应该设为`alias`而不是`root`
:::


## 部署博客

将本地`~/.ssh/id_rsa.pub`复制到服务器`~/.ssh/authorized_keys`之后即可免密登录。

本地 build ，然后打包上传
```
ssh ltzhou@ltzhou.com "cd ~; rm -rf www; mkdir www"
cd docs/.vuepress/dist; tar -zcf - ./ | ssh ltzhou@ltzhou.com "tar -zxf - -C ~/www"
```