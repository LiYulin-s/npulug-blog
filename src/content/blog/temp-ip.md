---
title: 西工大临时校域IP地址获取
pubDate: 2026-8-10
slug: access-campus-wide-ip-address
authors:
  - name: RainbowC0
    url: https://cnblogs.com/RainbowC0
---

> 省流：用 EasyConnect 分配的 IP 地址

## 背景

学校里很多时候自己的电脑放在宿舍，然后人在教室，但是需要访问电脑的资源；或者希望线上给同学老师一个可快速访问的 URL 用以展示自己的工作。面对这类情况，获取一个临时校域 IP 不失为一个好办法。

## 校园网现状

学校里连校园网最直接的办法就是连 NWPU-FREE 和 NWPU-WLAN 两个 WiFi，另外就是用网线拨号上网。但是学校的校园网有 AP 隔离，结果就是大家都连上了校园网但是彼此不可 ping 通（用 `iw` 之类的工具扫描可以发现实际上 NWPU-FREE 或者 NWPU-WLAN 有若干相同 SSID 的接入点）。

## 获取临时校域 IP 地址

对于身在校外的同学，访问校园网的方法就是用 EasyConnect 登陆自己的网络账号连接校园网，也就是学校的 VPN。这个 VPN 的 IP 地址恰好是校域可访问的。

![bi](/images/easy-connect.png)

如图，该 IPv4 地址`10.129.1.35`可用于校域内访问。我们在设备上运行如下命令启动一个 HTTP 服务器：

```shell
python -m http.server
```

该服务器在默认端口 8000 上运行。在校园网内其他设备上（不论是用 WiFi、网线还是 VPN）访问 <http://10.129.1.35:8000> 均可以看到页面。

另外，通过 VPN 连上校园网的用户可以直接访问其他设备的校园网 IP，不论对方是用哪种方式连接的校园网。

## 干货：常用服务器

- SSH(远程登陆)

```shell
sshd
```

- VPN(远程桌面)

```shell
vncserver
```

- HTTP(网页)

```shell
python -m http.server
busybox httpd
```

- FTP(文件传输)

```shell
busybox tcpsvd -vE 0.0.0.0 21 busybox ftpd /file/to/path
```

- WebDAV(文件传输)

```shell
dufs -A
```
