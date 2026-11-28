module github.com/conao3/lean-leangage/samples/go

go 1.27

require (
	github.com/conao3/lean-leangage/langs/go v0.0.0-00010101000000-000000000000
	github.com/conao3/leanfran-go v0.14.0
	github.com/jackc/pgx/v5 v5.13.0
)

require (
	github.com/jackc/pgpassfile v1.0.0 // indirect
	github.com/jackc/pgservicefile v0.0.0-20240606120523-5a60cdf6a761 // indirect
	github.com/jackc/puddle/v2 v2.2.3 // indirect
	golang.org/x/sync v0.22.0 // indirect
	golang.org/x/text v0.41.0 // indirect
)

replace github.com/conao3/lean-leangage/langs/go => ../../langs/go
