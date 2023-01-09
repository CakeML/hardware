Some notes about OpenTheory:

Docker image:

```
docker pull binghelisp/hol-dev:latest
docker run -ti --rm -v /tmp:/hgfs binghelisp/hol-dev:latest
```

OpenTheory commands:

```
opentheory info --theorems -o bool.art bool
opentheory info --document -o bool.html bool
```
